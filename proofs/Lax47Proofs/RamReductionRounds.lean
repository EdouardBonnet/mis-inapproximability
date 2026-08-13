import Lax47Proofs.RamReductionCounter

/-!
The fixed polynomially bounded sequence of resampling rounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionSemantics

open Lax47.Machine Lax47.Complexity Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

lemma advanceExecutionCounts_le_succ {n : ℕ}
    (counts : EdgeVariable n → ℕ) (selection : Option (ExecutionTriple n))
    (edge : EdgeVariable n) :
    advanceExecutionCounts counts selection edge ≤ counts edge + 1 := by
  cases selection <;> simp [advanceExecutionCounts]
  split <;> omega

lemma executeRounds_zero_counts_le {n : ℕ} (graph : GraphCode n)
    (seed : ExecutionSeed n) (rounds : ℕ) (edge : EdgeVariable n) :
    (executeRounds graph seed rounds (fun _ => 0)).1 edge ≤ rounds := by
  induction rounds with
  | zero => simp [executeRounds]
  | succ rounds ih =>
      simp only [executeRounds]
      have hstep := advanceExecutionCounts_le_succ
        (executeRounds graph seed rounds (fun _ => 0)).1
        (findExecutionViolation graph seed
          (executeRounds graph seed rounds (fun _ => 0)).1).1 edge
      omega

def RoundInvariant {n : ℕ} (graph : GraphCode n) (seed : ExecutionSeed n)
    (input : BitString) (state : Env) : Prop :=
  state.vars roundVar ≤ executionBudget n ∧
  ExecutionContext n input
    (executeRounds graph seed (state.vars roundVar) (fun _ => 0)).1 state

theorem resamplingRoundBody_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B) :
    let seed := executionSeedOfFlat flatSeed
    let tripleCount := (n * n) * (n * n) * (n * n)
    let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
    let scanBodyCost := testCost + 200
    let scanCost := (scanBodyCost + 4) * tripleCount + 100
    let roundCost := scanCost + 450
    Spec B
      (fun state => RoundInvariant graph seed input state ∧
        state.vars roundVar < executionBudget n)
      (Com.block [scanTriples, advanceCounters, increment roundVar])
      (fun initial final => RoundInvariant graph seed input final ∧
        final.vars roundVar = initial.vars roundVar + 1)
      roundCost := by
  dsimp only
  let seed := executionSeedOfFlat flatSeed
  let tripleCount := (n * n) * (n * n) * (n * n)
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  let scanBodyCost := testCost + 200
  let scanCost := (scanBodyCost + 4) * tripleCount + 100
  let roundCost := scanCost + 450
  unfold Spec
  intro initial hstate
  rcases hstate with ⟨hinvariant, hroundLt⟩
  rcases hinvariant with ⟨_hroundLe, hcontext⟩
  let rounds := initial.vars roundVar
  let counts := (executeRounds graph seed rounds (fun _ => 0)).1
  have hcountsLe (edge : EdgeVariable n) : counts edge ≤ rounds :=
    executeRounds_zero_counts_le graph seed rounds edge
  have hcountsB (edge : EdgeVariable n) : counts edge < B := by
    have := hcountsLe edge
    omega
  have hcountsSuccB (edge : EdgeVariable n) : counts edge + 1 < B := by
    have := hcountsLe edge
    omega
  obtain ⟨afterScan, hrunScan, hcontextScan, _hrankScan,
    hselectionScan⟩ :=
    (scanTriples_spec B input graph flatSeed model counts hn hB htripleB hinputB
      hvaluesB hbudgetB hsampleB hcountLenB hcountsB).run
        (by simpa [counts, rounds] using hcontext)
  obtain ⟨afterAdvance, hrunAdvance, hcontextAdvance⟩ :=
    (advanceCounters_spec B input counts
      (findExecutionViolation graph seed counts).1 (by omega) hcountLenB
      hcountsSuccB).run ⟨hcontextScan, hselectionScan⟩
  have hroundScan : afterScan.vars roundVar = rounds := by
    exact (hrunScan.frame_var roundVar (by decide)).trans rfl
  have hroundAdvance : afterAdvance.vars roundVar = rounds := by
    exact (hrunAdvance.frame_var roundVar (by decide)).trans hroundScan
  have hroundNextB : rounds + 1 < B := by omega
  have hroundAdvanceB : afterAdvance.vars roundVar < B := by
    rw [hroundAdvance]
    omega
  have hroundEval :
      (Expr.add (.var roundVar) (.lit 1)).evalB B afterAdvance =
        some (rounds + 1) := by
    have hvar := evalB_var hroundAdvanceB
    rw [hroundAdvance] at hvar
    exact evalB_bin hvar (evalB_lit (by omega))
      (by simpa using hroundNextB)
  let final := afterAdvance.setVar roundVar (rounds + 1)
  have hrunIncrement :
      Run B (increment roundVar) afterAdvance final 4 := by
    exact Run.assign hroundEval
  have hrunAll := Run.seq hrunScan
    (Run.seq hrunAdvance (Run.seq hrunIncrement Run.skip))
  have hfinalContext :
      ExecutionContext n input
        (executeRounds graph seed (rounds + 1) (fun _ => 0)).1 final := by
    simpa [final, ExecutionContext, HasRawInput, HasParameters,
      CountsRepresent, Env.setVar, executeRounds, counts, rounds, seed,
      rawLenVar, orderVar, blowupVar, countLenVar, tripleLenVar, budgetVar,
      sampleTargetVar, sampleBitsVar, roundVar, countsArray, rawArray] using
        hcontextAdvance
  have hfinalInvariant : RoundInvariant graph seed input final := by
    refine ⟨?_, ?_⟩
    · simp [final]
      omega
    · simpa [final] using hfinalContext
  refine ⟨final, ?_, hfinalInvariant, ?_⟩
  · simpa using hrunAll.mono (K' := roundCost) (by
      dsimp [roundCost, scanCost, scanBodyCost, testCost, tripleCount]
      omega)
  · simp [final, rounds]

/-- The complete fixed resampling loop realizes the pure bounded execution. -/
theorem resamplingRounds_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B) :
    let seed := executionSeedOfFlat flatSeed
    let tripleCount := (n * n) * (n * n) * (n * n)
    let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
    let scanBodyCost := testCost + 200
    let scanCost := (scanBodyCost + 4) * tripleCount + 100
    let roundCost := scanCost + 450
    let totalCost := (roundCost + 4) * executionBudget n + 100
    Spec B
      (ExecutionContext n input (fun _ => 0))
      resamplingRounds
      (fun _ final =>
        ExecutionContext n input (executionCounts graph seed) final ∧
        final.vars roundVar = executionBudget n)
      totalCost := by
  dsimp only
  let seed := executionSeedOfFlat flatSeed
  let tripleCount := (n * n) * (n * n) * (n * n)
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  let scanBodyCost := testCost + 200
  let scanCost := (scanBodyCost + 4) * tripleCount + 100
  let roundCost := scanCost + 450
  let totalCost := (roundCost + 4) * executionBudget n + 100
  let invariant := RoundInvariant graph seed input
  have hbodyBase := resamplingRoundBody_spec B input graph flatSeed model hn hB
    htripleB hinputB hvaluesB hbudgetB hsampleB hcountLenB
  have hbody :
      Spec B
        (fun state => invariant state ∧
          state.vars roundVar < executionBudget n)
        (Com.block [scanTriples, advanceCounters, increment roundVar])
        (fun initial final => invariant final ∧
          final.vars roundVar = initial.vars roundVar + 1)
        roundCost := by
    simpa only [seed, tripleCount, testCost, scanBodyCost, scanCost,
      roundCost] using hbodyBase
  have hloop := Spec.forRangeZero roundVar budgetVar invariant
    (executionBudget n) roundCost (by omega)
    (fun _ hstate => hstate.1)
    (fun _ hstate => by
      simpa only [invariant, RoundInvariant] using
        hstate.2.2.1.2.2.2.2.1)
    hbody
  apply hloop.conseq
  · intro state hcontext
    simpa [invariant, RoundInvariant, executeRounds, ExecutionContext,
      HasRawInput, HasParameters, CountsRepresent, Env.setVar, roundVar,
      rawLenVar, orderVar, blowupVar, countLenVar, tripleLenVar, budgetVar,
      sampleTargetVar, sampleBitsVar, countsArray, rawArray] using hcontext
  · intro _ final _ hpost
    rcases hpost with ⟨⟨_hroundLe, hfinalContext⟩, hfinalRound⟩
    refine ⟨?_, hfinalRound⟩
    simpa [invariant, executionCounts, hfinalRound] using hfinalContext
  · dsimp [totalCost, roundCost, scanCost, scanBodyCost, testCost,
      tripleCount]
    omega

end Lax47Proofs.RamReductionSemantics
