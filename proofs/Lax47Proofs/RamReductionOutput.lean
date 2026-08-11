import Lax47Proofs.RamReductionRounds
import Lax47Proofs.Redirect

/-!
Construction of the encoded output graph after the bounded resampling run.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionSemantics

open Lax47.Machine Lax47.Complexity Lax47.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

def HasOutputPair {n : ℕ} (left right : Fin (n * n)) (state : Env) : Prop :=
  let u := decodeBlowupVertex left
  let v := decodeBlowupVertex right
  state.vars firstVar = left.1 ∧ state.vars secondVar = right.1 ∧
  state.vars firstBaseVar = u.1.1 ∧
  state.vars secondBaseVar = v.1.1 ∧
  state.vars edgeOneVar = edgeSlot s(u, v)

def OutputInvariant {n : ℕ} (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n) (state : Env) : Prop :=
  let target := executionOutput graph (executionSeedOfFlat flatSeed)
  state.vars outputIndexVar ≤ (n * n) * (n * n) ∧
  ExecutionContext n input
    (executionCounts graph (executionSeedOfFlat flatSeed)) state ∧
  state.vars haltedVar = bitWord (executionHalted graph
    (executionSeedOfFlat flatSeed)) ∧
  state.arrs graphArray =
    target.bits.take (state.vars outputIndexVar + 1) ++
      List.replicate
        (target.bits.length - (state.vars outputIndexVar + 1)) 0

lemma blowupRank_decodeBlowupVertex {n : ℕ} (vertex : Fin (n * n)) :
    blowupRank (decodeBlowupVertex vertex) = vertex.1 := by
  unfold blowupRank decodeBlowupVertex
  simp
  exact Nat.mod_add_div vertex.1 n

lemma executionOutput_bits_at_rank {n i : ℕ} (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n) (hi : i < (n * n) * (n * n)) :
    let N := n * n
    let left : Fin N := ⟨i / N, Nat.div_lt_of_lt_mul (by simpa [N] using hi)⟩
    let right : Fin N := ⟨i % N, Nat.mod_lt _ (by
      have : 0 < n * n := by
        by_contra h
        have : n * n = 0 := Nat.eq_zero_of_not_pos h
        simp [this] at hi
      simpa [N] using this)⟩
    (executionOutput graph (executionSeedOfFlat flatSeed)).bits.getD (i + 1) 0 =
      bitWord ((executionOutput graph
        (executionSeedOfFlat flatSeed)).adjacent left right) := by
  dsimp only
  let N := n * n
  have hN : 0 < N := by
    by_contra h
    have hzero : N = 0 := Nat.eq_zero_of_not_pos h
    simp [N, hzero] at hi
  let left : Fin N := ⟨i / N, Nat.div_lt_of_lt_mul (by
    simpa [N] using hi)⟩
  let right : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩
  have hrank : 1 + left.1 * N + right.1 = i + 1 := by
    dsimp [left, right]
    calc
      1 + i / N * N + i % N =
          1 + (N * (i / N) + i % N) := by
            rw [Nat.mul_comm (i / N) N, Nat.add_assoc]
      _ = 1 + i := by rw [Nat.div_add_mod]
      _ = i + 1 := Nat.add_comm _ _
  rw [← GraphCode.bits_getD
    (executionOutput graph (executionSeedOfFlat flatSeed)) left right]
  exact congrArg
    (fun position ↦
      (executionOutput graph (executionSeedOfFlat flatSeed)).bits.getD position 0)
    hrank.symm

lemma executionOutput_bits_at_rank_halted {n i : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (hi : i < (n * n) * (n * n))
    (hhalted : executionHalted graph (executionSeedOfFlat flatSeed) = true) :
    let N := n * n
    let left : Fin N := ⟨i / N, Nat.div_lt_of_lt_mul (by simpa [N] using hi)⟩
    let right : Fin N := ⟨i % N, Nat.mod_lt _ (by
      have : 0 < n * n := by
        by_contra h
        have : n * n = 0 := Nat.eq_zero_of_not_pos h
        simp [this] at hi
      simpa [N] using this)⟩
    let u := decodeBlowupVertex left
    let v := decodeBlowupVertex right
    (executionOutput graph (executionSeedOfFlat flatSeed)).bits.getD (i + 1) 0 =
      bitWord (graph.adjacent u.1 v.1 &&
        executionCell (executionSeedOfFlat flatSeed) s(u, v)
          (executionCounts graph (executionSeedOfFlat flatSeed) s(u, v))) := by
  dsimp only
  rw [executionOutput_bits_at_rank graph flatSeed hi]
  simp [executionOutput, hhalted]

lemma executionOutput_bits_at_rank_not_halted {n i : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (hi : i < (n * n) * (n * n))
    (hhalted : executionHalted graph (executionSeedOfFlat flatSeed) = false) :
    (executionOutput graph (executionSeedOfFlat flatSeed)).bits.getD (i + 1) 0 = 0 := by
  rw [executionOutput_bits_at_rank graph flatSeed hi]
  simp [executionOutput, hhalted, bitWord]

theorem decodeOutputRanks_spec (B : ℕ) {n i : ℕ} (input : BitString)
    (counts : EdgeVariable n → ℕ) (hn : 0 < n)
    (hi : i < (n * n) * (n * n))
    (hcountLenB : (n * n) * (n * n) < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        state.vars outputIndexVar = i)
      decodeOutputRanks
      (fun _ final => ExecutionContext n input counts final ∧
        final.vars outputIndexVar = i ∧
        final.vars firstVar = i / (n * n) ∧
        final.vars secondVar = i % (n * n))
      100 := by
  have hNpos : 0 < n * n := Nat.mul_pos hn hn
  have hiB : i < B := hi.trans hcountLenB
  have hNB : n * n < B := by
    have hNle : n * n ≤ (n * n) * (n * n) := by
      nlinarith
    exact hNle.trans_lt hcountLenB
  have hquotB : i / (n * n) < B :=
    (Nat.div_le_self _ _).trans_lt hiB
  have hmulLe : i / (n * n) * (n * n) ≤ i :=
    Nat.div_mul_le_self _ _
  have hmulB : i / (n * n) * (n * n) < B := hmulLe.trans_lt hiB
  have hmodB : i % (n * n) < B := (Nat.mod_lt _ hNpos).trans hNB
  unfold decodeOutputRanks Com.block Spec
  intro state hstate
  rcases hstate with ⟨hcontext, hindex⟩
  run_vcg
  all_goals
    simp_all [ExecutionContext, HasRawInput, HasParameters, CountsRepresent,
      Env.setVar, Nat.mod_eq_sub_mul_div, Nat.mul_comm,
      outputIndexVar, firstVar, secondVar, rawLenVar, orderVar, blowupVar,
      countLenVar, tripleLenVar, budgetVar, sampleTargetVar, sampleBitsVar,
      countsArray, rawArray]
  all_goals omega

theorem outputPairPrelude_spec (B : ℕ) {n : ℕ} (input : BitString)
    (counts : EdgeVariable n → ℕ) (left right : Fin (n * n))
    (hn : 0 < n) (hcountLenB : (n * n) * (n * n) < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        state.vars firstVar = left.1 ∧ state.vars secondVar = right.1)
      outputPairPrelude
      (fun _ final => ExecutionContext n input counts final ∧
        HasOutputPair left right final)
      100 := by
  let u := decodeBlowupVertex left
  let v := decodeBlowupVertex right
  have hnB : n < B := by
    have hnN : n ≤ n * n := by nlinarith
    have hNB : n * n < B := by
      have hNpos : 0 < n * n := Nat.mul_pos hn hn
      calc
        n * n = (n * n) * 1 := by ring
        _ ≤ (n * n) * (n * n) := Nat.mul_le_mul_left _ (by omega)
        _ < B := hcountLenB
    omega
  have hNB : n * n < B := by
    have hNpos : 0 < n * n := Nat.mul_pos hn hn
    calc
      n * n = (n * n) * 1 := by ring
      _ ≤ (n * n) * (n * n) := Nat.mul_le_mul_left _ (by omega)
      _ < B := hcountLenB
  have hleftBase : left.1 / n = u.1.1 := by
    rw [← blowupRank_decodeBlowupVertex left]
    exact blowupRank_div_order hn u
  have hrightBase : right.1 / n = v.1.1 := by
    rw [← blowupRank_decodeBlowupVertex right]
    exact blowupRank_div_order hn v
  have hedge :
      canonicalSlot (n * n) left.1 right.1 = edgeSlot s(u, v) := by
    rw [← blowupRank_decodeBlowupVertex left,
      ← blowupRank_decodeBlowupVertex right]
    exact canonicalSlot_blowupRank u v
  have hpairLeft : left.1 * (n * n) + right.1 < B := by
    exact (by nlinarith [left.2, right.2] :
      left.1 * (n * n) + right.1 < (n * n) * (n * n)).trans hcountLenB
  have hpairRight : right.1 * (n * n) + left.1 < B := by
    exact (by nlinarith [left.2, right.2] :
      right.1 * (n * n) + left.1 < (n * n) * (n * n)).trans hcountLenB
  have hslot := edgeSlotCom_full_spec B firstVar secondVar edgeOneVar
  unfold outputPairPrelude Com.block
  run_vcg [hslot]
  all_goals
    simp_all [HasOutputPair, ExecutionContext, HasRawInput, HasParameters,
      CountsRepresent, Env.setVar, u, v, hleftBase, hrightBase, hedge,
      firstVar, secondVar, firstBaseVar, secondBaseVar, edgeOneVar,
      orderVar, blowupVar, countLenVar, tripleLenVar, budgetVar,
      sampleTargetVar, sampleBitsVar, rawLenVar, countsArray, rawArray]
  all_goals try omega

theorem requireGraphAdjacency_output_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ) (left right : Fin (n * n))
    (initialOk : ℕ)
    (hnB : n < B)
    (hgraphB : 2 + n * n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B) :
    let u := decodeBlowupVertex left
    let v := decodeBlowupVertex right
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        HasOutputPair left right state ∧ state.vars okVar = initialOk)
      (requireGraphAdjacency firstBaseVar secondBaseVar)
      (fun _ final =>
        ExecutionContext n input counts final ∧
        HasOutputPair left right final ∧
        final.vars okVar = retainIf initialOk (graph.adjacent u.1 v.1))
      250 := by
  dsimp only
  let u := decodeBlowupVertex left
  let v := decodeBlowupVertex right
  have hposition (a b : Fin n) : 2 + a.1 * n + b.1 < B := by
    have hab : a.1 * n + b.1 < n * n := by
      nlinarith [a.2, b.2]
    omega
  have hbase := requireGraphAdjacency_context_spec B input graph flatSeed model counts
    u.1 v.1 firstBaseVar secondBaseVar initialOk hnB
    (hposition u.1 v.1) (hposition v.1 u.1) hinputB hvaluesB
    (by decide) (by decide)
  have hframe := hbase.frame
  apply hframe.conseq
  · intro state hstate
    exact ⟨hstate.1, hstate.2.1.2.2.1, hstate.2.1.2.2.2.1, hstate.2.2⟩
  · intro initial final hpre hpost
    rcases hpre with ⟨_hcontext, hpair, _hok⟩
    rcases hpost with
      ⟨⟨hcontext, _hleft, _hright, hok⟩, hvars, _harrs, _hinp, _hout⟩
    have hkeep (name : String) (hOk : name ≠ okVar)
        (hRawIndex : name ≠ rawIndexVar) (hTemp : name ≠ tempVar) :
        final.vars name = initial.vars name := by
      apply hvars
      simp [requireGraphAdjacency, requireRawAdjacencyDirection,
        Com.block, readRawBit, setZero, setOne, Com.wvars,
        hOk, hRawIndex, hTemp]
    refine ⟨hcontext, ?_, hok⟩
    simpa only [HasOutputPair,
      hkeep firstVar (by decide) (by decide) (by decide),
      hkeep secondVar (by decide) (by decide) (by decide),
      hkeep firstBaseVar (by decide) (by decide) (by decide),
      hkeep secondBaseVar (by decide) (by decide) (by decide),
      hkeep edgeOneVar (by decide) (by decide) (by decide)] using hpair
  · rfl

theorem requireSampledEdge_output_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ) (left right : Fin (n * n))
    (initialOk : ℕ)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let u := decodeBlowupVertex left
    let v := decodeBlowupVertex right
    let edge : EdgeVariable n := s(u, v)
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        HasOutputPair left right state ∧ state.vars okVar = initialOk)
      (requireSampledEdge edgeOneVar)
      (fun _ final =>
        ExecutionContext n input counts final ∧
        HasOutputPair left right final ∧
        final.vars okVar = retainIf initialOk
          (executionCell (executionSeedOfFlat flatSeed) edge (counts edge)))
      ((200 + 4) * executionSampleBits n + 100) := by
  dsimp only
  let u := decodeBlowupVertex left
  let v := decodeBlowupVertex right
  let edge : EdgeVariable n := s(u, v)
  have hbase := requireSampledEdge_spec B input graph flatSeed model counts edge edgeOneVar
    initialOk hB hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
    (by decide)
  have hframe := hbase.frame
  apply hframe.conseq
  · intro state hstate
    exact ⟨hstate.1, hstate.2.1.2.2.2.2, hstate.2.2⟩
  · intro initial final hpre hpost
    rcases hpre with ⟨_hcontext, hpair, _hok⟩
    rcases hpost with ⟨⟨hcontext, _hedge, hok⟩, hvars, _harrs, _hinp, _hout⟩
    have hkeep (name : String) (hRow : name ≠ rowVar)
        (hRawIndex : name ≠ rawIndexVar) (hTemp : name ≠ tempVar)
        (hOk : name ≠ okVar) (hBit : name ≠ bitVar) :
        final.vars name = initial.vars name := by
      apply hvars
      simp [requireSampledEdge, sampleBlockLoop, sampleBitBody,
        readRawBit, Com.block, increment, setZero, setOne, Com.wvars,
        hRow, hRawIndex, hTemp, hOk, hBit]
    refine ⟨hcontext, ?_, hok⟩
    simpa only [HasOutputPair,
      hkeep firstVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep secondVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep firstBaseVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep secondBaseVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep edgeOneVar (by decide) (by decide) (by decide) (by decide) (by decide)]
      using hpair
  · rfl

theorem testOutputEdge_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ) (left right : Fin (n * n))
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let u := decodeBlowupVertex left
    let v := decodeBlowupVertex right
    let edge : EdgeVariable n := s(u, v)
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        state.vars firstVar = left.1 ∧ state.vars secondVar = right.1)
      testOutputEdge
      (fun _ final =>
        ExecutionContext n input counts final ∧
        HasOutputPair left right final ∧
        final.vars okVar = bitWord
          (graph.adjacent u.1 v.1 &&
            executionCell (executionSeedOfFlat flatSeed) edge (counts edge)))
      (500 + ((200 + 4) * executionSampleBits n + 100)) := by
  dsimp only
  let u := decodeBlowupVertex left
  let v := decodeBlowupVertex right
  let edge : EdgeVariable n := s(u, v)
  have hnB : n < B := by
    have hnN : n ≤ n * n := by nlinarith
    omega
  have hprelude := outputPairPrelude_spec B
    input counts left right hn hcountLenB
  have hadj := requireGraphAdjacency_output_spec B input graph flatSeed model counts
    left right 1 hnB (by omega) hinputB hvaluesB
  let afterAdj := retainIf 1 (graph.adjacent u.1 v.1)
  have hsample := requireSampledEdge_output_spec B input graph flatSeed model counts
    left right afterAdj hB hinputB hvaluesB hbudgetB hsampleB
    hcountLenB hcountsB
  let StateAt (value : ℕ) (state : Env) : Prop :=
    ExecutionContext n input counts state ∧
    HasOutputPair left right state ∧ state.vars okVar = value
  have hOneB : 1 < B := by omega
  have hsetOne :
      Spec B
        (fun state => ExecutionContext n input counts state ∧
          HasOutputPair left right state)
        (setOne okVar) (fun _ final => StateAt 1 final) 2 := by
    unfold Spec setOne
    intro state hstate
    refine ⟨state.setVar okVar 1, Run.assign (evalB_lit hOneB), ?_⟩
    rcases hstate with ⟨hcontext, hpair⟩
    simpa [StateAt, ExecutionContext, HasRawInput, HasParameters,
      CountsRepresent, HasOutputPair, Env.setVar, rawLenVar, orderVar,
      blowupVar, countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
      sampleBitsVar, firstVar, secondVar, firstBaseVar, secondBaseVar,
      edgeOneVar, okVar, countsArray, rawArray] using
        (show ExecutionContext n input counts state ∧
            HasOutputPair left right state ∧ 1 = 1 from
          ⟨hcontext, hpair, rfl⟩)
  have hadj' :
      Spec B (StateAt 1)
        (requireGraphAdjacency firstBaseVar secondBaseVar)
        (fun _ final => StateAt afterAdj final) 250 := by
    apply hadj.conseq
    · intro state hstate
      exact hstate
    · intro _ final _ hpost
      simpa [StateAt, afterAdj] using hpost
    · rfl
  have hsample' :
      Spec B (StateAt afterAdj) (requireSampledEdge edgeOneVar)
        (fun _ final => StateAt
          (retainIf afterAdj
            (executionCell (executionSeedOfFlat flatSeed) edge (counts edge))) final)
        ((200 + 4) * executionSampleBits n + 100) := by
    apply hsample.conseq
    · intro state hstate
      exact hstate
    · intro _ final _ hpost
      simpa [StateAt] using hpost
    · rfl
  have hfinalValue :
      retainIf afterAdj
          (executionCell (executionSeedOfFlat flatSeed) edge (counts edge)) =
        bitWord (graph.adjacent u.1 v.1 &&
          executionCell (executionSeedOfFlat flatSeed) edge (counts edge)) := by
    change retainIf (retainIf 1 (graph.adjacent u.1 v.1)) _ = _
    rw [retainIf_one, retainIf_bitWord]
  unfold Spec
  intro initial hinitial
  obtain ⟨afterPrelude, runPrelude, postPrelude⟩ := hprelude.run hinitial
  obtain ⟨afterSet, runSet, postSet⟩ := hsetOne.run postPrelude
  obtain ⟨afterAdjState, runAdj, postAdj⟩ := hadj'.run postSet
  obtain ⟨final, runSample, postFinal⟩ := hsample'.run postAdj
  refine ⟨final, ?_, ?_⟩
  · unfold testOutputEdge Com.block
    have hrun := runPrelude.seq (runSet.seq (runAdj.seq
      (runSample.seq (Run.skip (B := B) (σ := final)))))
    exact hrun.mono (by omega)
  · rcases postFinal with ⟨hcontext, hpair, hok⟩
    exact ⟨hcontext, hpair, hok.trans hfinalValue⟩

theorem outputLoopBody_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B) :
    let sampleCost := (200 + 4) * executionSampleBits n + 100
    let bodyCost := 1000 + sampleCost
    Spec B
      (fun state => OutputInvariant input graph flatSeed state ∧
        state.vars outputIndexVar < (n * n) * (n * n))
      outputLoopBody
      (fun initial final => OutputInvariant input graph flatSeed final ∧
        final.vars outputIndexVar = initial.vars outputIndexVar + 1)
      bodyCost := by
  dsimp only
  let seed := executionSeedOfFlat flatSeed
  let counts := executionCounts graph seed
  let target := executionOutput graph seed
  let N := n * n
  let count := N * N
  let sampleCost := (200 + 4) * executionSampleBits n + 100
  let bodyCost := 1000 + sampleCost
  have hNpos : 0 < N := by dsimp [N]; exact Nat.mul_pos hn hn
  have hNB : N < B := by
    have hNle : N ≤ count := by
      dsimp [count]
      nlinarith
    exact hNle.trans_lt (by simpa [N, count] using hcountLenB)
  have hOneB : 1 < B := by omega
  have hbitWordB (value : Bool) : bitWord value < B := by
    cases value <;> simp [bitWord] <;> omega
  have hcountsB (edge : EdgeVariable n) : counts edge < B := by
    have hle := executeRounds_zero_counts_le graph seed
      (executionBudget n) edge
    simpa [counts, executionCounts] using (show counts edge < B by
      dsimp [counts, executionCounts]
      omega)
  unfold Spec
  intro initial hpre
  rcases hpre with ⟨hinvariant, hindexLt⟩
  rcases hinvariant with ⟨_hindexLe, hcontext, hhalted, harray⟩
  let i := initial.vars outputIndexVar
  have harray' : initial.arrs graphArray =
      target.bits.take (i + 1) ++
        List.replicate (target.bits.length - (i + 1)) 0 := by
    simpa [i, target, seed] using harray
  have hi : i < count := by simpa [i, N, count] using hindexLt
  have hiB : i < B := hi.trans (by simpa [N, count] using hcountLenB)
  have hleftLt : i / N < N := Nat.div_lt_of_lt_mul hi
  have hrightLt : i % N < N := Nat.mod_lt _ hNpos
  let left : Fin N := ⟨i / N, hleftLt⟩
  let right : Fin N := ⟨i % N, hrightLt⟩
  let targetBit := target.bits.getD (i + 1) 0
  obtain ⟨afterDecode, runDecode, contextDecode, indexDecode,
      firstDecode, secondDecode⟩ :=
    (decodeOutputRanks_spec B input counts hn
      (by simpa [N, count] using hi) hcountLenB).run
        ⟨by simpa [counts, seed] using hcontext, rfl⟩
  have graphDecode : afterDecode.arrs graphArray = initial.arrs graphArray :=
    runDecode.frame_arr graphArray (by decide)
  have haltedDecode : afterDecode.vars haltedVar = bitWord
      (executionHalted graph seed) := by
    rw [runDecode.frame_var haltedVar (by decide)]
    exact hhalted
  have htest := testOutputEdge_spec B input graph flatSeed model counts left right hn hB
    hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
  obtain ⟨afterTest, runBranch, contextTest, okTest, indexTest,
      graphTest, haltedTest, targetBitB⟩ :
      ∃ afterTest,
        Run B
          (.ite (.eq (.var haltedVar) (.lit 1))
            testOutputEdge (setZero okVar))
          afterDecode afterTest (600 + sampleCost) ∧
        ExecutionContext n input counts afterTest ∧
        afterTest.vars okVar = targetBit ∧
        afterTest.vars outputIndexVar = i ∧
        afterTest.arrs graphArray = initial.arrs graphArray ∧
        afterTest.vars haltedVar = bitWord (executionHalted graph seed) ∧
        targetBit < B := by
    by_cases hhalt : executionHalted graph seed = true
    · have hhaltedB : afterDecode.vars haltedVar < B := by
        rw [haltedDecode, hhalt]
        simp [bitWord]
        omega
      have hcondition :
          (Cond.eq (.var haltedVar) (.lit 1)).evalB B afterDecode =
            some true :=
        (evalB_condEq (evalB_var hhaltedB) (evalB_lit hOneB)).trans
          (by simp [haltedDecode, hhalt, bitWord])
      obtain ⟨final, runTest, contextFinal, _pairFinal, okFinal⟩ :=
        htest.run ⟨contextDecode, firstDecode, by
          simpa [N, i] using secondDecode⟩
      have htarget := executionOutput_bits_at_rank_halted graph flatSeed
        (by simpa [N, count] using hi) hhalt
      refine ⟨final, ?_, contextFinal, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Run.ite_true hcondition runTest).mono (by
          dsimp [sampleCost]
          omega)
      · exact okFinal.trans (by simpa [targetBit, target, seed, N, left,
          right] using htarget.symm)
      · exact (runTest.frame_var outputIndexVar
          (by decide)).trans indexDecode
      · exact (runTest.frame_arr graphArray
          (by decide)).trans graphDecode
      · exact (runTest.frame_var haltedVar
          (by decide)).trans haltedDecode
      · dsimp [targetBit, target, seed]
        rw [htarget]
        exact hbitWordB _
    · have hhaltFalse : executionHalted graph seed = false := by
        exact Bool.eq_false_iff.mpr hhalt
      have hhaltedB : afterDecode.vars haltedVar < B := by
        rw [haltedDecode, hhaltFalse]
        simp [bitWord]
        omega
      have hcondition :
          (Cond.eq (.var haltedVar) (.lit 1)).evalB B afterDecode =
            some false :=
        (evalB_condEq (evalB_var hhaltedB) (evalB_lit hOneB)).trans
          (by simp [haltedDecode, hhaltFalse, bitWord])
      let final := afterDecode.setVar okVar 0
      have runZero : Run B (setZero okVar) afterDecode final 2 := by
        exact Run.assign (evalB_lit (by omega))
      have htarget := executionOutput_bits_at_rank_not_halted graph flatSeed
        (by simpa [N, count] using hi) hhaltFalse
      have contextFinal :
          ExecutionContext n input counts final := by
        simpa [final, ExecutionContext, HasRawInput, HasParameters,
          CountsRepresent, Env.setVar, okVar, rawLenVar, orderVar, blowupVar,
          countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
          sampleBitsVar, countsArray, rawArray] using contextDecode
      refine ⟨final, ?_, contextFinal, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Run.ite_false hcondition runZero).mono (by
          dsimp [sampleCost]
          omega)
      · calc
          final.vars okVar = 0 := by simp [final, Env.setVar, okVar]
          _ = targetBit := by
            dsimp [targetBit, target, seed]
            exact htarget.symm
      · simpa [final, Env.setVar, outputIndexVar, okVar] using indexDecode
      · simpa [final, Env.setVar] using graphDecode
      · simpa [final, Env.setVar, haltedVar, okVar] using haltedDecode
      · have hzero : targetBit = 0 := by
          dsimp [targetBit, target, seed]
          exact htarget
        rw [hzero]
        omega
  have htargetLength : target.bits.length = count + 1 := by
    simpa [count, N, Nat.add_comm] using GraphCode.bits_length target
  have hprefixLe : i + 1 ≤ target.bits.length := by
    rw [htargetLength]
    omega
  have harrayLength : (initial.arrs graphArray).length = target.bits.length := by
    rw [harray', List.length_append, List.length_replicate,
      List.length_take_of_le hprefixLe]
    omega
  have hstoreIndex : i + 1 < (afterTest.arrs graphArray).length := by
    rw [graphTest, harrayLength, htargetLength]
    omega
  have hindexTestB : afterTest.vars outputIndexVar < B := by
    rw [indexTest]
    exact hiB
  have hstorePositionB : i + 1 < B := by omega
  have hstoreIndexEval :
      (Expr.add (.var outputIndexVar) (.lit 1)).evalB B afterTest =
        some (i + 1) := by
    exact evalB_bin (by simpa [indexTest] using evalB_var hindexTestB)
      (evalB_lit hOneB) (by simpa using hstorePositionB)
  have hstoreValueEval :
      (Expr.var okVar).evalB B afterTest = some targetBit := by
    have hokB : afterTest.vars okVar < B := by
      rw [okTest]
      exact targetBitB
    simpa [okTest] using evalB_var hokB
  let afterStore := afterTest.setArr graphArray (i + 1) targetBit
  have runStore :
      Run B
        (.store graphArray (.add (.var outputIndexVar) (.lit 1))
          (.var okVar))
        afterTest afterStore 10 := by
    exact (Run.store hstoreIndexEval hstoreValueEval hstoreIndex).mono
      (by simp [Expr.size])
  have hnextB : i + 1 < B := by omega
  have hnextEval :
      (Expr.add (.var outputIndexVar) (.lit 1)).evalB B afterStore =
        some (i + 1) := by
    have hindexStore : afterStore.vars outputIndexVar = i := by
      simpa [afterStore, Env.setArr] using indexTest
    exact evalB_bin (by
      simpa [hindexStore] using evalB_var (show afterStore.vars outputIndexVar < B by
        rw [hindexStore]
        exact hiB)) (evalB_lit hOneB) (by simpa using hnextB)
  let final := afterStore.setVar outputIndexVar (i + 1)
  have runIncrement : Run B (increment outputIndexVar) afterStore final 4 :=
    Run.assign hnextEval
  have htakeLength : (target.bits.take (i + 1)).length = i + 1 :=
    List.length_take_of_le hprefixLe
  have hroom : (target.bits.take (i + 1)).length + 1 ≤ target.bits.length := by
    rw [htakeLength, htargetLength]
    omega
  have htakeNext :
      target.bits.take (i + 2) =
        target.bits.take (i + 1) ++ [targetBit] := by
    rw [show i + 2 = (i + 1) + 1 by omega, List.take_add_one]
    have hposition : i + 1 < target.bits.length := by
      rw [htargetLength]
      omega
    rw [List.getElem?_eq_getElem hposition]
    simp only [Option.toList_some]
    congr 2
    simp [targetBit, List.getElem?_eq_getElem hposition]
  have harrayFinal : final.arrs graphArray =
      target.bits.take ((i + 1) + 1) ++
        List.replicate (target.bits.length - ((i + 1) + 1)) 0 := by
    have hcapture := Lax47Proofs.Redirect.capture_set
      (target.bits.take (i + 1)) target.bits.length targetBit hroom
    have hstored : afterStore.arrs graphArray =
        (initial.arrs graphArray).set (i + 1) targetBit := by
      simp [afterStore, graphTest, Env.setArr]
    rw [show final.arrs graphArray = afterStore.arrs graphArray by
      simp [final, Env.setVar], hstored, harray']
    simpa [htakeLength, htakeNext, List.length_append, Nat.add_assoc] using
      hcapture
  have contextFinal :
      ExecutionContext n input counts final := by
    simpa [final, afterStore, ExecutionContext, HasRawInput, HasParameters,
      CountsRepresent, Env.setVar, Env.setArr, outputIndexVar, graphArray,
      rawLenVar, orderVar, blowupVar, countLenVar, tripleLenVar, budgetVar,
      sampleTargetVar, sampleBitsVar, countsArray, rawArray] using contextTest
  have haltedFinal : final.vars haltedVar = bitWord
      (executionHalted graph seed) := by
    simpa [final, afterStore, Env.setVar, Env.setArr, haltedVar,
      outputIndexVar] using haltedTest
  have finalInvariant : OutputInvariant input graph flatSeed final := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [final]
      omega
    · simpa [counts, seed] using contextFinal
    · simpa [seed] using haltedFinal
    · simpa [final, target, seed, harrayFinal]
  refine ⟨final, ?_, finalInvariant, ?_⟩
  · unfold outputLoopBody Com.block
    have runAll := runDecode.seq (runBranch.seq
      (runStore.seq (runIncrement.seq (Run.skip (B := B) (σ := final)))))
    exact runAll.mono (by
      dsimp [bodyCost, sampleCost]
      omega)
  · simp [final, i]

theorem buildOutputGraph_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B) :
    let seed := executionSeedOfFlat flatSeed
    let counts := executionCounts graph seed
    let target := executionOutput graph seed
    let count := (n * n) * (n * n)
    let sampleCost := (200 + 4) * executionSampleBits n + 100
    let bodyCost := 1000 + sampleCost
    let totalCost := (bodyCost + 4) * count + 100
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        state.vars haltedVar = bitWord (executionHalted graph seed) ∧
        state.arrs graphArray = List.replicate target.bits.length 0)
      buildOutputGraph
      (fun _ final =>
        ExecutionContext n input counts final ∧
        final.vars haltedVar = bitWord (executionHalted graph seed) ∧
        final.arrs graphArray = target.bits)
      totalCost := by
  dsimp only
  let seed := executionSeedOfFlat flatSeed
  let counts := executionCounts graph seed
  let target := executionOutput graph seed
  let count := (n * n) * (n * n)
  let sampleCost := (200 + 4) * executionSampleBits n + 100
  let bodyCost := 1000 + sampleCost
  let totalCost := (bodyCost + 4) * count + 100
  have hcountB : count < B := by simpa [count] using hcountLenB
  have hNB : n * n < B := by
    have hle : n * n ≤ count := by
      dsimp [count]
      nlinarith
    exact hle.trans_lt hcountB
  have hzeroB : 0 < B := by omega
  have htargetLength : target.bits.length = count + 1 := by
    simpa [target, count, Nat.add_comm] using GraphCode.bits_length target
  have hbody :
      Spec B
        (fun state => OutputInvariant input graph flatSeed state ∧
          state.vars outputIndexVar < count)
        outputLoopBody
        (fun initial final => OutputInvariant input graph flatSeed final ∧
          final.vars outputIndexVar = initial.vars outputIndexVar + 1)
        bodyCost := by
    simpa [count, bodyCost, sampleCost] using
      outputLoopBody_spec B input graph flatSeed model hn hB hinputB hvaluesB
        hbudgetB hsampleB hcountLenB
  have hloop := Spec.forRangeZero outputIndexVar countLenVar
    (OutputInvariant input graph flatSeed) count bodyCost hcountB
    (fun _ state => state.1)
    (fun _ state => by
      rcases state with ⟨_index, context, _halted, _array⟩
      exact context.2.1.2.2.1)
    hbody
  unfold Spec
  intro initial hpre
  rcases hpre with ⟨hcontext, hhalted, harray⟩
  have hblowup : initial.vars blowupVar = n * n := hcontext.2.1.2.1
  have hblowupB : initial.vars blowupVar < B := by
    rw [hblowup]
    exact hNB
  have hindexEval : (Expr.lit 0).evalB B initial = some 0 :=
    evalB_lit hzeroB
  have hvalueEval : (Expr.var blowupVar).evalB B initial = some (n * n) := by
    simpa [hblowup] using evalB_var hblowupB
  have hroom : 0 < (initial.arrs graphArray).length := by
    rw [harray, List.length_replicate, htargetLength]
    omega
  let afterHeader := initial.setArr graphArray 0 (n * n)
  have runHeader :
      Run B (.store graphArray (.lit 0) (.var blowupVar))
        initial afterHeader 10 := by
    exact (Run.store hindexEval hvalueEval hroom).mono (by simp [Expr.size])
  have contextHeader :
      ExecutionContext n input counts afterHeader := by
    simpa [afterHeader, ExecutionContext, HasRawInput, HasParameters,
      CountsRepresent, Env.setArr, graphArray, rawArray, countsArray] using
        hcontext
  have haltedHeader : afterHeader.vars haltedVar =
      bitWord (executionHalted graph seed) := by
    simpa [afterHeader, Env.setArr] using hhalted
  have harrayLocal : initial.arrs graphArray =
      List.replicate target.bits.length 0 := by
    simpa [target, seed] using harray
  have arrayHeader : afterHeader.arrs graphArray =
      target.bits.take 1 ++ List.replicate (target.bits.length - 1) 0 := by
    have hcapture := Lax47Proofs.Redirect.capture_set
      ([] : List ℕ) target.bits.length (n * n) (by
        rw [htargetLength]
        simp)
    have htargetHead : target.bits.take 1 = [n * n] := by
      simp [target, GraphCode.bits]
    rw [show afterHeader.arrs graphArray =
        (List.replicate target.bits.length 0).set 0 (n * n) by
      simp [afterHeader, harrayLocal, Env.setArr]]
    simpa [htargetHead] using hcapture
  have hloopPre : OutputInvariant input graph flatSeed
      (afterHeader.setVar outputIndexVar 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Env.setVar]
    · simpa [counts, seed, ExecutionContext, HasRawInput, HasParameters,
        CountsRepresent, Env.setVar, outputIndexVar, rawLenVar, orderVar,
        blowupVar, countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
        sampleBitsVar, countsArray, rawArray] using contextHeader
    · simpa [seed, Env.setVar, outputIndexVar, haltedVar] using haltedHeader
    · simpa [target, seed, Env.setVar, outputIndexVar] using arrayHeader
  obtain ⟨final, runLoop, finalInvariant, finalIndex⟩ :=
    hloop.run hloopPre
  rcases finalInvariant with ⟨_indexLe, contextFinal, haltedFinal, arrayFinal⟩
  have finalArray : final.arrs graphArray = target.bits := by
    rw [finalIndex] at arrayFinal
    have arrayFinal' : final.arrs graphArray =
        target.bits.take (count + 1) ++
          List.replicate (target.bits.length - (count + 1)) 0 := by
      simpa [target, seed] using arrayFinal
    have htake : target.bits.take (count + 1) = target.bits :=
      List.take_of_length_le (by rw [htargetLength])
    simpa [htargetLength, htake] using arrayFinal'
  refine ⟨final, ?_, ?_, ?_, finalArray⟩
  · unfold buildOutputGraph Com.block
    have runAll := runHeader.seq
      (runLoop.seq (Run.skip (B := B) (σ := final)))
    have hcost : 10 + (((bodyCost + 4) * count + 6) + 1) ≤
        totalCost := by
      dsimp [totalCost]
      omega
    have hrun := runAll.mono (K' := totalCost) hcost
    simpa [totalCost, bodyCost, sampleCost, count] using hrun
  · simpa [counts, seed] using contextFinal
  · simpa [seed] using haltedFinal

end Lax47Proofs.RamReductionSemantics
