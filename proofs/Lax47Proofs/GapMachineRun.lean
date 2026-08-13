import Lax47Proofs.GapMachine

/-!
Plain IMP+ execution of the complete gap machine.  This is the semantic
seam between the already verified reduction, Lax51's native simulation of
the supplied approximation machine, and the elementary final passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Lax47Proofs.GapMachine

open Lax47.Machine Lax47.Complexity Lax47.Gap
open Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax47Proofs.RamReductionSemantics Lax47Proofs.Redirect
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

/-- Maximum entry in a finite input word. -/
def inputMax : BitString → ℕ
  | [] => 0
  | value :: rest => max value (inputMax rest)

lemma mem_le_inputMax {input : BitString} {value : ℕ}
    (membership : value ∈ input) : value ≤ inputMax input := by
  induction input with
  | nil => simp at membership
  | cons head tail ih =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact le_max_left _ _
      · exact (ih membership).trans (le_max_right _ _)

lemma mem_redirectCom_wvars {command : Com} {name : String}
    (membership : name ∈ (redirectCom command).wvars) :
    name = inputCursor ∨ name = outputCursor ∨
      ∃ sourceName, name = algorithmName sourceName := by
  induction command with
  | skip => simp [redirectCom, Com.wvars] at membership
  | assign source expression =>
      simp [redirectCom, Com.wvars] at membership
      exact Or.inr (Or.inr ⟨source, membership⟩)
  | store source index expression =>
      simp [redirectCom, Com.wvars] at membership
  | seq first second firstIH secondIH =>
      simp only [redirectCom, Com.wvars, List.mem_append] at membership
      exact membership.elim firstIH secondIH
  | ite condition yes no yesIH noIH =>
      simp only [redirectCom, Com.wvars, List.mem_append] at membership
      exact membership.elim yesIH noIH
  | «while» condition body bodyIH =>
      simp only [redirectCom, Com.wvars] at membership
      exact bodyIH membership
  | read source =>
      simp [redirectCom, redirectRead, increment, Com.wvars] at membership
      rcases membership with membership | membership
      · exact Or.inr (Or.inr ⟨source, membership⟩)
      · exact Or.inl membership
  | write expression =>
      simp [redirectCom, redirectWrite, increment, Com.wvars] at membership
      exact Or.inr (Or.inl membership)

lemma redirectCom_var_eq {command : Com} {initial final : Env} {cost : ℕ}
    (run : BigStep (redirectCom command) initial final cost)
    (name : String) (hinput : name ≠ inputCursor)
    (houtput : name ≠ outputCursor)
    (hhead : name.toList.head? = some 'r') :
    final.vars name = initial.vars name := by
  apply run.vars_eq
  intro membership
  rcases mem_redirectCom_wvars membership with equality | equality | ⟨source, equality⟩
  · exact hinput equality
  · exact houtput equality
  · exact (algorithmName_ne_of_head_r source name hhead) equality.symm

lemma redirectCom_noWrite (command : Com) :
    (redirectCom command).NoWrite := by
  induction command with
  | skip => simp [redirectCom, Com.NoWrite]
  | assign => simp [redirectCom, Com.NoWrite]
  | store => simp [redirectCom, Com.NoWrite]
  | seq first second firstIH secondIH =>
      simp [redirectCom, Com.NoWrite, firstIH, secondIH]
  | ite condition yes no yesIH noIH =>
      simp [redirectCom, Com.NoWrite, yesIH, noIH]
  | «while» condition body bodyIH =>
      simp [redirectCom, Com.NoWrite, bodyIH]
  | read => simp [redirectCom, redirectRead, increment, Com.NoWrite]
  | write => simp [redirectCom, redirectWrite, increment, Com.NoWrite]

lemma algorithmName_not_mem_reductionAfterDecode_wvars (name : String) :
    algorithmName name ∉ reductionAfterDecode.wvars := by
  have heads : ∀ target ∈ reductionAfterDecode.wvars,
      target.toList.head? = some 'r' := by
    set_option maxRecDepth 100000 in
      decide
  intro membership
  exact (algorithmName_ne_of_head_r name _ (heads _ membership)) rfl

lemma algorithmName_not_mem_reductionAfterDecode_warrs (name : String) :
    algorithmName name ∉ reductionAfterDecode.warrs := by
  have heads : ∀ target ∈ reductionAfterDecode.warrs,
      target.toList.head? = some 'r' := by
    set_option maxRecDepth 100000 in
      decide
  intro membership
  exact (algorithmName_ne_of_head_r name _ (heads _ membership)) rfl

/-- One deliberately redundant finite bound satisfying every local bound
hypothesis of the verified reduction semantics.  It need not itself be a
complexity bound; the IMP cost below is the quantity used for that purpose. -/
def reductionValueBound (input : BitString) (n : ℕ) : ℕ :=
  1 + inputMax input + input.length + input.getD 1 0 +
    (2 + n * n + flatRandomBitCount n) +
    ((n * n) * (n * n) * (n * n) + 1) +
    (executionBudget n + 1) + executionSampleBits n +
    ((n * n) * (n * n)) +
    (2 * (100 * (n + 1) + 1)) +
    (12 * (n + 1) ^ 6) + (executionSampleBits n + 1)

/-- The explicit cost appearing in `reductionCom_model_spec`. -/
def reductionCostBound (inputLength n : ℕ) : ℕ :=
  let tripleCount := (n * n) * (n * n) * (n * n)
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  let scanBodyCost := testCost + 200
  let scanCost := (scanBodyCost + 4) * tripleCount + 100
  let roundCost := scanCost + 450
  let roundsCost := (roundCost + 4) * executionBudget n + 100
  let outputBodyCost := 1000 + ((200 + 4) * executionSampleBits n + 100)
  let outputCost := (outputBodyCost + 4) * ((n * n) * (n * n)) + 100
  let sampleComputeCost := 30 * (executionSampleBits n + 1) + 20
  let preludeCost := 1 + 12 * inputLength + 7
  preludeCost + 40 + 100 + sampleComputeCost + roundsCost + scanCost +
    20 + outputCost + 100

/-- The verified reduction command terminates on every nonzero decoded
order, and produces the semantic finite Moser--Tardos graph. -/
theorem reductionCom_raw_bigStep (sourceExt : String → ℕ)
    (input : BitString) (n : ℕ) (hn : 0 < n)
    (horder : rawOrder input = n) (outputCapacity : ℕ) :
    let graph := rawGraphCodeAt n input
    let flatSeed := rawFlatSeedAt n input
    let target := executionOutput graph (executionSeedOfFlat flatSeed)
    let ext := combinedExt sourceExt input ((n * n) * (n * n))
      target.bits.length outputCapacity
    ∃ final cost,
      BigStep reductionCom (initEnv ext (input.length :: input)) final cost ∧
      ExecutionContext n input
        (executionCounts graph (executionSeedOfFlat flatSeed)) final ∧
      final.vars haltedVar =
        bitWord (executionHalted graph (executionSeedOfFlat flatSeed)) ∧
      final.arrs graphArray = target.bits ∧
      cost ≤ reductionCostBound input.length n := by
  dsimp only
  let graph := rawGraphCodeAt n input
  let flatSeed := rawFlatSeedAt n input
  let target := executionOutput graph (executionSeedOfFlat flatSeed)
  let ext := combinedExt sourceExt input ((n * n) * (n * n))
    target.bits.length outputCapacity
  let B := reductionValueBound input n
  have hvalue (value : ℕ) (membership : value ∈ input) : value < B := by
    have := mem_le_inputMax membership
    dsimp [B, reductionValueBound]
    omega
  have hspec := reductionCom_model_spec B ext input graph flatSeed
    (ModelsReductionInput.raw n input) horder hn
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    hvalue
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by simp [ext]) (by simp [ext]) (by simp [ext, target])
  obtain ⟨final, run, context, halted, graphOutput⟩ :=
    hspec.run (by rfl)
  obtain ⟨cost, hcost, bigStep⟩ := run.bigStep
  refine ⟨final, cost, bigStep, context, halted, graphOutput, ?_⟩
  simpa [reductionCostBound] using hcost

/-- End-to-end execution on the nonzero branch.  In particular, the call to
the approximation is the actual Lax51 native machine run, redirected through
the graph and output arrays. -/
theorem gapCom_positive_bigStep (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString)
    (hn : 0 < rawOrder input) :
    let n := rawOrder input
    let graph := rawGraphCodeAt n input
    let flatSeed := rawFlatSeedAt n input
    let target := executionOutput graph (executionSeedOfFlat flatSeed)
    let outputBits := algorithm.program.output target.bits
    ∃ ext final cost,
      BigStep (gapCom q algorithm) (initEnv ext (input.length :: input))
        final cost ∧
      final.out =
        (if n ^ (q + 3) ≤ (decodeVertexSet (n * n) outputBits).card ^ q
          then [1] else [0]) ∧
      cost ≤ reductionCostBound input.length n +
        20 * approximationNativeCost algorithm target.bits outputBits +
        40 * (n * n) + 10 * (q + 5) + 100 := by
  dsimp only
  let n := rawOrder input
  let graph := rawGraphCodeAt n input
  let flatSeed := rawFlatSeedAt n input
  let target := executionOutput graph (executionSeedOfFlat flatSeed)
  let outputBits := algorithm.program.output target.bits
  obtain ⟨sourceExt, sourceFinal, sourceCost, sourceRun, sourceOut,
    sourceCostBound⟩ := approximationNativeCom_bigStep algorithm target.bits
  let capacity := outputBits.length + n * n
  let ext := combinedExt sourceExt input ((n * n) * (n * n))
    target.bits.length capacity
  obtain ⟨afterReduction, reductionCost, reductionRun, reductionContext,
      _reductionHalted, reductionGraph, reductionCostLe⟩ :=
    reductionCom_raw_bigStep sourceExt input n (by simpa [n] using hn)
      (by rfl) capacity
  change BigStep (.seq inputPrelude (.seq decodeOrder reductionAfterDecode))
    (initEnv ext (input.length :: input)) afterReduction reductionCost at reductionRun
  cases reductionRun with
  | seq preludeRun decodedRun =>
    cases decodedRun with
    | seq decodeRun reductionTailRun =>
      rename_i afterPrelude preludeCost afterDecode decodeCost reductionTailCost
      have wholeReductionRun : BigStep reductionCom
          (initEnv ext (input.length :: input)) afterReduction
          (preludeCost + (decodeCost + reductionTailCost)) := by
        simpa [reductionCom] using
          BigStep.seq preludeRun (BigStep.seq decodeRun reductionTailRun)
      have initialRelation : Rel target.bits capacity
          (initEnv sourceExt (target.bits.length :: target.bits))
          afterReduction := by
        constructor
        · intro name
          rw [wholeReductionRun.vars_eq
            (algorithmName_not_mem_reduction_wvars name)]
          simp [initEnv]
        · intro name
          rw [wholeReductionRun.arrs_eq
            (algorithmName_not_mem_reduction_warrs name)]
          simp [initEnv, ext, combinedExt_algorithmName]
        · have hcursor : afterReduction.vars inputCursor = 0 := by
            rw [wholeReductionRun.vars_eq (by decide)]
            simp [initEnv]
          simp [hcursor, virtualInput]
        · have hcursor : afterReduction.vars inputCursor = 0 := by
            rw [wholeReductionRun.vars_eq (by decide)]
            simp [initEnv]
          simp [initEnv, virtualInput, hcursor]
        · simp [initEnv, capacity]
        · have hcursor : afterReduction.vars outputCursor = 0 := by
            rw [wholeReductionRun.vars_eq (by decide)]
            simp [initEnv]
          simp [initEnv, hcursor]
        · have harray : afterReduction.arrs algorithmOutputArray =
              List.replicate capacity 0 := by
            rw [wholeReductionRun.arrs_eq (by decide)]
            simp [initEnv, ext]
          simpa [initEnv, harray]
        · exact reductionGraph
        · have hcount := reductionContext.2.1.2.2.1
          rw [hcount, graphCode_bits_length]
          omega
      have sourceCapacity : sourceFinal.out.length ≤ capacity := by
        rw [sourceOut]
        simp [outputBits, capacity]
      obtain ⟨afterAlgorithm, redirectedCost, redirectedRun,
          redirectedRelation, redirectedCostBound⟩ :=
        redirectCom_bigStep sourceRun initialRelation sourceCapacity
      have redirectedBlowup : afterAlgorithm.vars blowupVar = n * n := by
        rw [redirectCom_var_eq redirectedRun blowupVar (by decide)
          (by decide) (by decide)]
        exact reductionContext.2.1.2.1
      have redirectedOrder : afterAlgorithm.vars orderVar = n := by
        rw [redirectCom_var_eq redirectedRun orderVar (by decide)
          (by decide) (by decide)]
        exact reductionContext.2.1.1
      have redirectedArray : afterAlgorithm.arrs algorithmOutputArray =
          outputBits ++ List.replicate (n * n) 0 := by
        rw [redirectedRelation.output_array, sourceOut]
        simp [outputBits, capacity]
      have reductionOut : afterReduction.out = [] := by
        have hall : reductionCom.NoWrite := by decide
        simpa [initEnv] using wholeReductionRun.out_eq hall
      have redirectedOut : afterAlgorithm.out = [] := by
        rw [redirectedRun.out_eq (redirectCom_noWrite _)]
        exact reductionOut
      obtain ⟨afterCount, countCost, countRun, countCard, countIndex,
          _countArray, countCostBound⟩ :=
        countAlgorithmOutput_bigStep outputBits (n * n) afterAlgorithm
          redirectedBlowup redirectedArray
      have countOrder : afterCount.vars orderVar = n := by
        rw [countRun.vars_eq (by decide)]
        exact redirectedOrder
      have countOut : afterCount.out = [] := by
        rw [countRun.out_eq (by decide)]
        exact redirectedOut
      have countCardDecoded : afterCount.vars outputCardVar =
          (decodeVertexSet (n * n) outputBits).card := by
        rw [countCard, oneCount_eq_decodeVertexSet_card]
      obtain ⟨final, decisionCost, decisionRun, decisionOut,
          decisionCostBound⟩ := writeGapDecision_bigStep q n
        (decodeVertexSet (n * n) outputBits).card afterCount countOrder
        countCardDecoded countOut
      have positiveRun : BigStep (positiveGapCom q algorithm) afterDecode final
          (reductionTailCost +
            (redirectedCost + (countCost + (decisionCost + 1)))) := by
        simpa [positiveGapCom, Com.block] using
          BigStep.seq reductionTailRun
            (BigStep.seq redirectedRun
              (BigStep.seq countRun (BigStep.seq decisionRun BigStep.skip)))
      have decodeOrderValue : afterDecode.vars orderVar = n := by
        rw [← reductionTailRun.vars_eq (by decide)]
        exact reductionContext.2.1.1
      have conditionFalse :
          (Cond.eq (.var orderVar) (.lit 0)).eval afterDecode = some false := by
        simp [Cond.eval, decodeOrderValue]
        omega
      let totalCost := preludeCost + (decodeCost +
        (1 + (Cond.eq (.var orderVar) (.lit 0)).size +
          (reductionTailCost +
            (redirectedCost + (countCost + (decisionCost + 1))))))
      have wholeRun : BigStep (gapCom q algorithm)
          (initEnv ext (input.length :: input)) final totalCost := by
        dsimp only [totalCost]
        exact BigStep.seq preludeRun (BigStep.seq decodeRun
          (BigStep.ite_false conditionFalse positiveRun))
      refine ⟨ext, final, totalCost, wholeRun, decisionOut, ?_⟩
      change totalCost ≤ reductionCostBound input.length n +
        20 * approximationNativeCost algorithm target.bits outputBits +
        40 * (n * n) + 10 * (q + 5) + 100
      dsimp only [totalCost]
      simp only [Cond.size, Expr.size]
      have countCostBoundN : countCost ≤ 40 * (n * n) + 30 :=
        countCostBound
      have sourceCostBound' : sourceCost ≤
          approximationNativeCost algorithm target.bits outputBits := by
        simpa [outputBits] using sourceCostBound
      omega

/-- The total decoder returns false when its capped graph order is zero. -/
theorem gapCom_zero_bigStep (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString)
    (hzero : rawOrder input = 0) :
    ∃ ext final cost,
      BigStep (gapCom q algorithm) (initEnv ext (input.length :: input))
        final cost ∧
      final.out = [0] ∧ cost ≤ 12 * input.length + 100 := by
  let ext := combinedExt (fun _ => 0) input 0 0 0
  let B := reductionValueBound input 0
  have hvalue (value : ℕ) (membership : value ∈ input) : value < B := by
    have := mem_le_inputMax membership
    dsimp [B, reductionValueBound]
    omega
  have hpreludeBase := readScalarsThenArr_spec B ext [rawLenVar]
    rawArray loadIndexVar rawLenVar tempVar [input.length] input
    (by simp) (by simp) (by simp) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp [ext])
    (by dsimp [B, reductionValueBound]; omega) hvalue
  have hprelude : Spec B
      (fun state => state = initEnv ext (input.length :: input)) inputPrelude
      (fun _ final => ScalarsArrIn ext [rawLenVar] rawArray loadIndexVar
        tempVar [input.length] input final)
      (1 + 12 * input.length + 7) := by
    simpa [inputPrelude] using hpreludeBase
  obtain ⟨afterPrelude, preludeRun, preludePost⟩ :=
    hprelude.run (by rfl)
  have rawPrelude : HasRawInput input afterPrelude := by
    exact ⟨preludePost.cells (rawLenVar, input.length) (by simp),
      preludePost.arr⟩
  obtain ⟨afterDecode, decodeRun, _rawDecode, orderDecode⟩ :=
    (decodeOrder_spec B input).run
      ⟨rawPrelude,
        by dsimp [B, reductionValueBound]; omega,
        by dsimp [B, reductionValueBound]; omega,
        by rw [hzero]; dsimp [B, reductionValueBound]; omega,
        by dsimp [B, reductionValueBound]; omega⟩
  have orderZero : afterDecode.vars orderVar = 0 := by
    rw [orderDecode, hzero]
  have conditionTrue :
      (Cond.eq (.var orderVar) (.lit 0)).eval afterDecode = some true := by
    simp [Cond.eval, orderZero]
  let final : Env := { afterDecode with out := afterDecode.out ++ [0] }
  have decodeOut : afterDecode.out = [] := by
    rw [decodeRun.out_eq (by decide)]
    rw [preludeRun.out_eq (by decide)]
    simp [initEnv]
  have writeRun : BigStep (.write (.lit 0)) afterDecode final 2 := by
    exact BigStep.write rfl
  obtain ⟨preludeCost, preludeCostBound, preludeBig⟩ := preludeRun.bigStep
  obtain ⟨decodeCost, decodeCostBound, decodeBig⟩ := decodeRun.bigStep
  let totalCost := preludeCost + (decodeCost +
    (1 + (Cond.eq (.var orderVar) (.lit 0)).size + 2))
  have wholeRun : BigStep (gapCom q algorithm)
      (initEnv ext (input.length :: input)) final totalCost := by
    dsimp only [totalCost]
    simpa [gapCom] using BigStep.seq preludeBig (BigStep.seq decodeBig
      (BigStep.ite_true conditionTrue writeRun))
  refine ⟨ext, final, totalCost, wholeRun, ?_, ?_⟩
  · simp [final, decodeOut]
  · dsimp only [totalCost]
    simp only [Cond.size, Expr.size]
    omega

/-- Total word function computed by the composed gap machine. -/
noncomputable def gapFunction (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString) :
    BitString :=
  let n := rawOrder input
  if n = 0 then [0]
  else
    let graph := rawGraphCodeAt n input
    let flatSeed := rawFlatSeedAt n input
    let target := executionOutput graph (executionSeedOfFlat flatSeed)
    let outputBits := algorithm.program.output target.bits
    if n ^ (q + 3) ≤ (decodeVertexSet (n * n) outputBits).card ^ q
      then [1] else [0]

theorem gapCom_bigStep (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString) :
    ∃ ext final cost,
      BigStep (gapCom q algorithm) (initEnv ext (input.length :: input))
        final cost ∧
      final.out = gapFunction q algorithm input ∧
      cost ≤ 12 * input.length + 100 +
        reductionCostBound input.length (rawOrder input) +
        20 * approximationNativeCost algorithm
          (rawReductionGraphBits input)
          (algorithm.program.output (rawReductionGraphBits input)) +
        40 * (rawOrder input * rawOrder input) + 10 * (q + 5) + 100 := by
  by_cases hzero : rawOrder input = 0
  · obtain ⟨ext, final, cost, run, output, costBound⟩ :=
      gapCom_zero_bigStep q algorithm input hzero
    refine ⟨ext, final, cost, run, ?_, ?_⟩
    · simpa [gapFunction, hzero] using output
    · omega
  · have hn : 0 < rawOrder input := Nat.pos_of_ne_zero hzero
    obtain ⟨ext, final, cost, run, output, costBound⟩ :=
      gapCom_positive_bigStep q algorithm input hn
    refine ⟨ext, final, cost, run, ?_, ?_⟩
    · simpa [gapFunction, hzero, rawReductionGraphBits, rawGraphCode,
        rawFlatSeed] using output
    · have htarget :
          (executionOutput (rawGraphCodeAt (rawOrder input) input)
            (executionSeedOfFlat (rawFlatSeedAt (rawOrder input) input))).bits =
            rawReductionGraphBits input := by
          rfl
      rw [htarget] at costBound
      exact costBound.trans (by omega)

end Lax47Proofs.GapMachine
