import Lax47Proofs.RamReductionOutput

/-!
End-to-end correctness of the fixed reduction command on a well-formed graph
and flat random tape.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionSemantics

open Lax47.Machine Lax47.Complexity Lax47.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

theorem setHaltedFlag_spec (B : ℕ) {n : ℕ} (input : BitString)
    (counts : EdgeVariable n → ℕ)
    (selection : Option (ExecutionTriple n)) (hOneB : 1 < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        SelectionRepresent selection state)
      (.ite (.eq (.var foundVar) (.lit 0))
        (setOne haltedVar) (setZero haltedVar))
      (fun _ final => ExecutionContext n input counts final ∧
        final.vars haltedVar = bitWord selection.isNone)
      20 := by
  unfold Spec
  intro initial hpre
  rcases hpre with ⟨hcontext, hselection⟩
  cases selection with
  | none =>
      have hfound : initial.vars foundVar = 0 := by
        simpa [SelectionRepresent] using hselection
      have hfoundB : initial.vars foundVar < B := by omega
      have hcondition :
          (Cond.eq (.var foundVar) (.lit 0)).evalB B initial = some true :=
        (evalB_condEq (evalB_var hfoundB) (evalB_lit (by omega))).trans
          (by simp [hfound])
      let final := initial.setVar haltedVar 1
      have hrunSet : Run B (setOne haltedVar) initial final 2 :=
        Run.assign (evalB_lit hOneB)
      refine ⟨final, (Run.ite_true hcondition hrunSet).mono (by
        simp [Cond.size, Expr.size]), ?_⟩
      simpa [final, ExecutionContext, HasRawInput, HasParameters,
        CountsRepresent, Env.setVar, SelectionRepresent, bitWord,
        haltedVar, rawLenVar, orderVar, blowupVar, countLenVar,
        tripleLenVar, budgetVar, sampleTargetVar, sampleBitsVar,
        rawArray, countsArray] using hcontext
  | some triple =>
      have hfound : initial.vars foundVar = 1 := by
        simpa [SelectionRepresent] using hselection.1
      have hfoundB : initial.vars foundVar < B := by omega
      have hcondition :
          (Cond.eq (.var foundVar) (.lit 0)).evalB B initial = some false :=
        (evalB_condEq (evalB_var hfoundB) (evalB_lit (by omega))).trans
          (by simp [hfound])
      let final := initial.setVar haltedVar 0
      have hrunSet : Run B (setZero haltedVar) initial final 2 :=
        Run.assign (evalB_lit (by omega))
      refine ⟨final, (Run.ite_false hcondition hrunSet).mono (by
        simp [Cond.size, Expr.size]), ?_⟩
      simpa [final, ExecutionContext, HasRawInput, HasParameters,
        CountsRepresent, Env.setVar, SelectionRepresent, bitWord,
        haltedVar, rawLenVar, orderVar, blowupVar, countLenVar,
        tripleLenVar, budgetVar, sampleTargetVar, sampleBitsVar,
        rawArray, countsArray] using hcontext

theorem reductionCom_model_spec (B : ℕ) (ext : String → ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (hrawOrder : rawOrder input = n)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : input.length < B)
    (hclaimedB : input.getD 1 0 < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hsampleLoopB : 2 * (100 * (n + 1) + 1) < B)
    (hcomputeBudgetB : 12 * (n + 1) ^ 6 < B)
    (hsampleSuccB : executionSampleBits n + 1 < B)
    (hextRaw : ext rawArray = input.length)
    (hextCounts : ext countsArray = (n * n) * (n * n))
    (hextGraph : ext graphArray =
      (executionOutput graph (executionSeedOfFlat flatSeed)).bits.length) :
    let seed := executionSeedOfFlat flatSeed
    let counts := executionCounts graph seed
    let target := executionOutput graph seed
    let tripleCount := (n * n) * (n * n) * (n * n)
    let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
    let scanBodyCost := testCost + 200
    let scanCost := (scanBodyCost + 4) * tripleCount + 100
    let roundCost := scanCost + 450
    let roundsCost := (roundCost + 4) * executionBudget n + 100
    let outputBodyCost := 1000 + ((200 + 4) * executionSampleBits n + 100)
    let outputCost := (outputBodyCost + 4) * ((n * n) * (n * n)) + 100
    let sampleComputeCost := 30 * (executionSampleBits n + 1) + 20
    let preludeCost := 1 + 12 * input.length + 7
    let totalCost := preludeCost + 40 + 100 + sampleComputeCost +
      roundsCost + scanCost + 20 + outputCost + 100
    Spec B
      (fun state => state = initEnv ext (input.length :: input))
      reductionCom
      (fun _ final =>
        ExecutionContext n input counts final ∧
        final.vars haltedVar = bitWord (executionHalted graph seed) ∧
        final.arrs graphArray = target.bits)
      totalCost := by
  dsimp only
  let seed := executionSeedOfFlat flatSeed
  let counts := executionCounts graph seed
  let target := executionOutput graph seed
  let tripleCount := (n * n) * (n * n) * (n * n)
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  let scanBodyCost := testCost + 200
  let scanCost := (scanBodyCost + 4) * tripleCount + 100
  let roundCost := scanCost + 450
  let roundsCost := (roundCost + 4) * executionBudget n + 100
  let outputBodyCost := 1000 + ((200 + 4) * executionSampleBits n + 100)
  let outputCost := (outputBodyCost + 4) * ((n * n) * (n * n)) + 100
  let sampleComputeCost := 30 * (executionSampleBits n + 1) + 20
  let preludeCost := 1 + 12 * input.length + 7
  let totalCost := preludeCost + 40 + 100 + sampleComputeCost +
    roundsCost + scanCost + 20 + outputCost + 100
  have hnB : n < B := by
    have hn2 : n ≤ n * n := by nlinarith
    omega
  have htargetB : 100 * (n + 1) + 1 < B := by omega
  have htriplePlainB : tripleCount < B := by
    dsimp [tripleCount]
    omega
  have hpreludeBase := readScalarsThenArr_spec B ext [rawLenVar]
    rawArray loadIndexVar rawLenVar tempVar [input.length] input
    (by simp) (by simp) (by simp) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simpa using hextRaw) hinputB hvaluesB
  have hprelude :
      Spec B (fun state => state = initEnv ext (input.length :: input))
        inputPrelude
        (fun _ final => ScalarsArrIn ext [rawLenVar] rawArray loadIndexVar
          tempVar [input.length] input final)
        preludeCost := by
    simpa [inputPrelude, preludeCost] using hpreludeBase
  unfold Spec
  intro initial hinitial
  obtain ⟨afterPrelude, runPrelude, postPrelude⟩ := hprelude.run hinitial
  have rawLenPrelude : afterPrelude.vars rawLenVar = input.length := by
    exact postPrelude.cells (rawLenVar, input.length) (by simp)
  have rawArrayPrelude : afterPrelude.arrs rawArray = input := postPrelude.arr
  have rawPrelude : HasRawInput input afterPrelude :=
    ⟨rawLenPrelude, rawArrayPrelude⟩
  have countsPrelude : afterPrelude.arrs countsArray =
      List.replicate ((n * n) * (n * n)) 0 := by
    rw [postPrelude.arrs countsArray (by decide), hextCounts]
  have graphPrelude : afterPrelude.arrs graphArray =
      List.replicate target.bits.length 0 := by
    rw [postPrelude.arrs graphArray (by decide)]
    simpa [target, seed] using hextGraph
  obtain ⟨afterDecode, runDecode, rawDecode, orderDecode⟩ :=
    (decodeOrder_spec B input).run
      ⟨rawPrelude, hinputB, hclaimedB,
        by rw [hrawOrder]; exact hnB, by omega⟩
  have orderDecodeN : afterDecode.vars orderVar = n := by
    rw [orderDecode, hrawOrder]
  have countsDecode : afterDecode.arrs countsArray =
      List.replicate ((n * n) * (n * n)) 0 := by
    rw [runDecode.frame_arr countsArray (by decide)]
    exact countsPrelude
  have graphDecode : afterDecode.arrs graphArray =
      List.replicate target.bits.length 0 := by
    rw [runDecode.frame_arr graphArray (by decide)]
    exact graphPrelude
  obtain ⟨afterParameters, runParameters, parameters⟩ :=
    (computeParameters_spec B n).run
      ⟨orderDecodeN, htargetB, hcomputeBudgetB, htriplePlainB⟩
  have rawParameters : HasRawInput input afterParameters := by
    refine ⟨?_, ?_⟩
    · rw [runParameters.frame_var rawLenVar (by decide)]
      exact rawDecode.1
    · rw [runParameters.frame_arr rawArray (by decide)]
      exact rawDecode.2
  have countsParameters : afterParameters.arrs countsArray =
      List.replicate ((n * n) * (n * n)) 0 := by
    rw [runParameters.frame_arr countsArray (by decide)]
    exact countsDecode
  have graphParameters : afterParameters.arrs graphArray =
      List.replicate target.bits.length 0 := by
    rw [runParameters.frame_arr graphArray (by decide)]
    exact graphDecode
  obtain ⟨afterSample, runSample, targetSample, sampleBitsSample, _powSample⟩ :=
    (computeSampleBits_spec B n hsampleLoopB hsampleSuccB).run
      parameters.2.2.2.2.2
  have rawSample : HasRawInput input afterSample := by
    refine ⟨?_, ?_⟩
    · rw [runSample.frame_var rawLenVar (by decide)]
      exact rawParameters.1
    · rw [runSample.frame_arr rawArray (by decide)]
      exact rawParameters.2
  have parametersSample : HasParameters n afterSample := by
    rcases parameters with ⟨horder, hblowup, hcount, htriple, hbudget, _target⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, targetSample⟩
    all_goals
      first
      | exact (runSample.frame_var _ (by decide)).trans horder
      | exact (runSample.frame_var _ (by decide)).trans hblowup
      | exact (runSample.frame_var _ (by decide)).trans hcount
      | exact (runSample.frame_var _ (by decide)).trans htriple
      | exact (runSample.frame_var _ (by decide)).trans hbudget
  have countsSample : afterSample.arrs countsArray =
      List.replicate ((n * n) * (n * n)) 0 := by
    rw [runSample.frame_arr countsArray (by decide)]
    exact countsParameters
  have graphSample : afterSample.arrs graphArray =
      List.replicate target.bits.length 0 := by
    rw [runSample.frame_arr graphArray (by decide)]
    exact graphParameters
  have zeroCounts : CountsRepresent n (fun _ => 0) afterSample := by
    refine ⟨?_, ?_⟩
    · rw [countsSample, List.length_replicate]
    · intro edge
      rw [countsSample]
      simp [List.getD_eq_getElem?_getD, edgeSlot_lt edge]
  have contextSample : ExecutionContext n input (fun _ => 0) afterSample :=
    ⟨rawSample, parametersSample, sampleBitsSample, zeroCounts⟩
  have hroundsBase := resamplingRounds_spec B input graph flatSeed model hn hB htripleB
    hinputB hvaluesB hbudgetB hsampleB hcountLenB
  have hrounds : Spec B (ExecutionContext n input (fun _ => 0))
      resamplingRounds
      (fun _ final => ExecutionContext n input counts final ∧
        final.vars roundVar = executionBudget n)
      roundsCost := by
    simpa [seed, counts, tripleCount, testCost, scanBodyCost,
      scanCost, roundCost, roundsCost] using hroundsBase
  obtain ⟨afterRounds, runRounds, contextRounds, _roundsDone⟩ :=
    hrounds.run contextSample
  have graphRounds : afterRounds.arrs graphArray =
      List.replicate target.bits.length 0 := by
    rw [runRounds.frame_arr graphArray (by decide)]
    exact graphSample
  have hcountsB (edge : EdgeVariable n) : counts edge < B := by
    have hle := executeRounds_zero_counts_le graph seed
      (executionBudget n) edge
    dsimp [counts, executionCounts]
    omega
  have hscanBase := scanTriples_spec B input graph flatSeed model counts hn hB htripleB
    hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
  have hscan : Spec B (ExecutionContext n input counts) scanTriples
      (fun _ final => ExecutionContext n input counts final ∧
        final.vars rankVar = tripleCount ∧
        SelectionRepresent (findExecutionViolation graph seed counts).1 final)
      scanCost := by
    simpa [seed, tripleCount, testCost, scanBodyCost, scanCost] using
      hscanBase
  obtain ⟨afterScan, runScan, contextScan, _rankScan, selectionScan⟩ :=
    hscan.run contextRounds
  have graphScan : afterScan.arrs graphArray =
      List.replicate target.bits.length 0 := by
    rw [runScan.frame_arr graphArray (by decide)]
    exact graphRounds
  have hhalt := setHaltedFlag_spec B input counts
    (findExecutionViolation graph seed counts).1 (by omega)
  obtain ⟨afterHalt, runHalt, contextHalt, haltedHalt⟩ :=
    hhalt.run ⟨contextScan, selectionScan⟩
  have haltedExpected : afterHalt.vars haltedVar =
      bitWord (executionHalted graph seed) := by
    simpa [executionHalted, counts] using haltedHalt
  have graphHalt : afterHalt.arrs graphArray =
      List.replicate target.bits.length 0 := by
    rw [runHalt.frame_arr graphArray (by decide)]
    exact graphScan
  have houtputBase := buildOutputGraph_spec B input graph flatSeed model hn hB hinputB
    hvaluesB hbudgetB hsampleB hcountLenB
  have houtput :
      Spec B
        (fun state => ExecutionContext n input counts state ∧
          state.vars haltedVar = bitWord (executionHalted graph seed) ∧
          state.arrs graphArray = List.replicate target.bits.length 0)
        buildOutputGraph
        (fun _ final => ExecutionContext n input counts final ∧
          final.vars haltedVar = bitWord (executionHalted graph seed) ∧
          final.arrs graphArray = target.bits)
        outputCost := by
    simpa [seed, counts, target, outputBodyCost, outputCost] using
      houtputBase
  obtain ⟨final, runOutput, contextFinal, haltedFinal, graphFinal⟩ :=
    houtput.run ⟨contextHalt, haltedExpected, graphHalt⟩
  refine ⟨final, ?_, contextFinal, haltedFinal, graphFinal⟩
  unfold reductionCom reductionAfterDecode Com.block
  have runAll := runPrelude.seq (runDecode.seq (runParameters.seq
    (runSample.seq (runRounds.seq (runScan.seq (runHalt.seq
      (runOutput.seq (Run.skip (B := B) (σ := final)))))))))
  have hcost : preludeCost + (40 + (100 + (sampleComputeCost +
      (roundsCost + (scanCost + (20 + (outputCost + 1))))))) ≤
      totalCost := by
    dsimp [totalCost]
    omega
  have hrun := runAll.mono (K' := totalCost) hcost
  simpa [totalCost, preludeCost, sampleComputeCost, roundsCost, roundCost,
    scanCost, scanBodyCost, testCost, tripleCount, outputCost,
    outputBodyCost] using hrun

end Lax47Proofs.RamReductionSemantics
