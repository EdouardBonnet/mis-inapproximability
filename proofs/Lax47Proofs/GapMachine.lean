import Lax47Proofs.RamReductionFull
import Lax47.Gap
import Lax51Proofs.RamToTM.PolynomialBounds

/-!
The complete Håstad-gap solver is one ordinary IMP+ program.  Its first
phase is the verified finite Moser--Tardos reduction.  Its second phase is
the Lax51 native interpreter for the supplied approximation Turing machine,
with input and output redirected to finite arrays.  The last two phases count
the returned vertices and perform the fixed rational threshold comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Lax47Proofs.GapMachine

open Lax47.Machine Lax47.Complexity Lax47.Gap
open Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax47Proofs.RamReductionSemantics Lax47Proofs.Redirect
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen
open Lax13Proofs.Compile Lax13Proofs.Simulation Lax13.Ram
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open Polynomial

def outputCardVar : String := "r.outputCard"
def decisionLeftVar : String := "r.decisionLeft"
def decisionRightVar : String := "r.decisionRight"

/-- Number of $1$ entries among the first `limit` positions, with missing
entries read as zero exactly as in `decodeVertexSet`. -/
def oneCount (bits : BitString) (limit : ℕ) : ℕ :=
  ((List.range limit).filter fun index => bits[index]?.getD 0 = 1).length

/-- One pass over the first `blowupVar` returned membership bits. -/
def countAlgorithmOutputBody : Com :=
  Com.block [
    .ite (.eq (.get algorithmOutputArray (.var outputIndexVar)) (.lit 1))
      (increment outputCardVar) .skip,
    increment outputIndexVar]

def countAlgorithmOutput : Com :=
  Com.block [
    setZero outputCardVar,
    setZero outputIndexVar,
    .while (.lt (.var outputIndexVar) (.var blowupVar))
      countAlgorithmOutputBody]

lemma getElem?_append_replicate_getD (bits : BitString) {limit index : ℕ}
    (hindex : index < limit) :
    (bits ++ List.replicate limit 0)[index]? = some (bits[index]?.getD 0) := by
  by_cases hin : index < bits.length
  · rw [List.getElem?_append_left hin]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin]
  · rw [List.getElem?_append_right (by omega)]
    have hright : index - bits.length < limit := by omega
    rw [List.getElem?_replicate]
    simp only [if_pos hright]
    have hnone : bits[index]? = none :=
      List.getElem?_eq_none (by omega)
    simp [hnone]

lemma oneCount_succ (bits : BitString) (index : ℕ) :
    oneCount bits (index + 1) = oneCount bits index +
      if bits[index]?.getD 0 = 1 then 1 else 0 := by
  simp only [oneCount, List.range_succ, List.filter_append,
    List.length_append, List.filter_singleton]
  split <;> simp_all

lemma option_getD_zero_eq_one (value : Option ℕ) :
    value.getD 0 = 1 ↔ value = some 1 := by
  cases value <;> simp

lemma oneCount_eq_decodeVertexSet_card (bits : BitString) (limit : ℕ) :
    oneCount bits limit = (decodeVertexSet limit bits).card := by
  classical
  let predicate : ℕ → Prop := fun index => bits[index]?.getD 0 = 1
  let embedding : Fin limit ↪ ℕ :=
    ⟨fun index => index.1, fun _ _ equality => Fin.ext equality⟩
  have hlist :
      (((List.range limit).filter predicate).toFinset) =
        (Finset.range limit).filter predicate := by
    ext index
    simp [predicate]
  have hmap :
      ((Finset.univ.filter fun index : Fin limit =>
          bits[index.1]? = some 1).map embedding) =
        (Finset.range limit).filter predicate := by
    ext index
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_range, embedding, predicate,
      option_getD_zero_eq_one]
    constructor
    · rintro ⟨mapped, hbit, rfl⟩
      exact ⟨mapped.2, hbit⟩
    · rintro ⟨hindex, hbit⟩
      exact ⟨⟨index, hindex⟩, hbit, rfl⟩
  unfold oneCount decodeVertexSet
  change ((List.range limit).filter predicate).length = _
  rw [← List.toFinset_card_of_nodup
    (List.nodup_range.filter _), hlist, ← hmap, Finset.card_map]

/-- State relation for the executable cardinality pass. -/
structure CountInvariant (bits : BitString) (limit : ℕ) (state : Env) : Prop where
  index_le : state.vars outputIndexVar ≤ limit
  blowup : state.vars blowupVar = limit
  array : state.arrs algorithmOutputArray = bits ++ List.replicate limit 0
  card : state.vars outputCardVar = oneCount bits (state.vars outputIndexVar)

theorem countAlgorithmOutputBody_bigStep (bits : BitString) (limit : ℕ)
    (initial : Env) (invariant : CountInvariant bits limit initial)
    (hindex : initial.vars outputIndexVar < limit) :
    ∃ final cost,
      BigStep countAlgorithmOutputBody initial final cost ∧
      CountInvariant bits limit final ∧
      final.vars outputIndexVar = initial.vars outputIndexVar + 1 ∧
      cost ≤ 30 := by
  let index := initial.vars outputIndexVar
  let value := bits[index]?.getD 0
  have hget :
      (Expr.get algorithmOutputArray (.var outputIndexVar)).eval initial =
        some value := by
    simp only [Expr.eval, Option.bind_some]
    rw [invariant.array]
    exact getElem?_append_replicate_getD bits hindex
  have hone : (Expr.lit 1).eval initial = some 1 := rfl
  by_cases hvalue : value = 1
  · let afterCard := initial.setVar outputCardVar
        (initial.vars outputCardVar + 1)
    let final := afterCard.setVar outputIndexVar
      (initial.vars outputIndexVar + 1)
    have hcondition :
        (Cond.eq (.get algorithmOutputArray (.var outputIndexVar))
          (.lit 1)).eval initial = some true := by
      simp [Cond.eval, hget, hvalue]
    have hcardEval :
        (Expr.add (.var outputCardVar) (.lit 1)).eval initial =
          some (initial.vars outputCardVar + 1) := by simp [Expr.eval]
    have hindexEval :
        (Expr.add (.var outputIndexVar) (.lit 1)).eval afterCard =
          some (initial.vars outputIndexVar + 1) := by
      simp [Expr.eval, afterCard, Env.setVar, outputCardVar, outputIndexVar]
    have hrunBranch : BigStep
        (.ite (.eq (.get algorithmOutputArray (.var outputIndexVar)) (.lit 1))
          (increment outputCardVar) .skip)
        initial afterCard 9 :=
      BigStep.ite_true hcondition (BigStep.assign hcardEval)
    have hrunIndex : BigStep (increment outputIndexVar) afterCard final 4 :=
      BigStep.assign hindexEval
    refine ⟨final, 14, ?_, ?_, by rfl, by omega⟩
    · exact BigStep.seq hrunBranch (BigStep.seq hrunIndex BigStep.skip)
    · constructor
      · change initial.vars outputIndexVar + 1 ≤ limit
        omega
      · have hIndex : blowupVar ≠ outputIndexVar := by decide
        have hCard : blowupVar ≠ outputCardVar := by decide
        simpa [final, afterCard, Env.setVar, hIndex,
          Ne.symm hIndex, hCard, Ne.symm hCard] using invariant.blowup
      · simpa [final, afterCard, Env.setVar] using invariant.array
      · have hvalue' : bits[initial.vars outputIndexVar]?.getD 0 = 1 := by
          simpa [value, index] using hvalue
        change initial.vars outputCardVar + 1 =
          oneCount bits (initial.vars outputIndexVar + 1)
        rw [invariant.card, oneCount_succ]
        simp [hvalue']
  · let final := initial.setVar outputIndexVar
      (initial.vars outputIndexVar + 1)
    have hcondition :
        (Cond.eq (.get algorithmOutputArray (.var outputIndexVar))
          (.lit 1)).eval initial = some false := by
      simp [Cond.eval, hget, hvalue]
    have hindexEval :
        (Expr.add (.var outputIndexVar) (.lit 1)).eval initial =
          some (initial.vars outputIndexVar + 1) := by simp [Expr.eval]
    have hrunBranch : BigStep
        (.ite (.eq (.get algorithmOutputArray (.var outputIndexVar)) (.lit 1))
          (increment outputCardVar) .skip)
        initial initial 6 := BigStep.ite_false hcondition BigStep.skip
    have hrunIndex : BigStep (increment outputIndexVar) initial final 4 :=
      BigStep.assign hindexEval
    refine ⟨final, 11, ?_, ?_, by rfl, by omega⟩
    · exact BigStep.seq hrunBranch (BigStep.seq hrunIndex BigStep.skip)
    · constructor
      · change initial.vars outputIndexVar + 1 ≤ limit
        omega
      · simpa [final, Env.setVar] using invariant.blowup
      · simpa [final, Env.setVar] using invariant.array
      · have hvalue' : bits[initial.vars outputIndexVar]?.getD 0 ≠ 1 := by
          simpa [value, index] using hvalue
        change initial.vars outputCardVar =
          oneCount bits (initial.vars outputIndexVar + 1)
        rw [invariant.card, oneCount_succ]
        simp [hvalue']

theorem countAlgorithmOutputLoop_bigStep (bits : BitString) (limit remaining : ℕ)
    (initial : Env) (invariant : CountInvariant bits limit initial)
    (hremaining : initial.vars outputIndexVar + remaining = limit) :
    ∃ final cost,
      BigStep (.while (.lt (.var outputIndexVar) (.var blowupVar))
        countAlgorithmOutputBody) initial final cost ∧
      CountInvariant bits limit final ∧
      final.vars outputIndexVar = limit ∧
      cost ≤ 40 * remaining + 10 := by
  induction remaining generalizing initial with
  | zero =>
      have hindex : initial.vars outputIndexVar = limit := by omega
      have hcondition :
          (Cond.lt (.var outputIndexVar) (.var blowupVar)).eval initial =
            some false := by simp [Cond.eval, invariant.blowup, hindex]
      exact ⟨initial, _, BigStep.while_false hcondition, invariant, hindex,
        by simp [Cond.size, Expr.size]⟩
  | succ remaining ih =>
      have hindex : initial.vars outputIndexVar < limit := by omega
      have hcondition :
          (Cond.lt (.var outputIndexVar) (.var blowupVar)).eval initial =
            some true := by simp [Cond.eval, invariant.blowup, hindex]
      obtain ⟨middle, bodyCost, bodyRun, middleInvariant, middleIndex,
        bodyBound⟩ := countAlgorithmOutputBody_bigStep bits limit initial
          invariant hindex
      have hmiddleRemaining :
          middle.vars outputIndexVar + remaining = limit := by omega
      obtain ⟨final, loopCost, loopRun, finalInvariant, finalIndex,
        loopBound⟩ := ih middle middleInvariant hmiddleRemaining
      refine ⟨final, _, BigStep.while_true hcondition bodyRun loopRun,
        finalInvariant, finalIndex, ?_⟩
      simp only [Cond.size, Expr.size]
      omega

theorem countAlgorithmOutput_bigStep (bits : BitString) (limit : ℕ)
    (initial : Env)
    (hblowup : initial.vars blowupVar = limit)
    (harray : initial.arrs algorithmOutputArray =
      bits ++ List.replicate limit 0) :
    ∃ final cost,
      BigStep countAlgorithmOutput initial final cost ∧
      final.vars outputCardVar = oneCount bits limit ∧
      final.vars outputIndexVar = limit ∧
      final.arrs algorithmOutputArray = bits ++ List.replicate limit 0 ∧
      cost ≤ 40 * limit + 30 := by
  let afterCard := initial.setVar outputCardVar 0
  let prepared := afterCard.setVar outputIndexVar 0
  have hrunCard : BigStep (setZero outputCardVar) initial afterCard 2 := by
    exact BigStep.assign rfl
  have hrunIndex : BigStep (setZero outputIndexVar) afterCard prepared 2 := by
    exact BigStep.assign rfl
  have hprepared : CountInvariant bits limit prepared := by
    constructor
    · simp [prepared, afterCard, Env.setVar, outputIndexVar]
    · simpa [prepared, afterCard, Env.setVar] using hblowup
    · simpa [prepared, afterCard, Env.setVar] using harray
    · simp [prepared, afterCard, Env.setVar, outputCardVar, outputIndexVar,
        oneCount]
  obtain ⟨final, loopCost, loopRun, finalInvariant, finalIndex, loopBound⟩ :=
    countAlgorithmOutputLoop_bigStep bits limit limit prepared hprepared (by
      simp [prepared, afterCard, Env.setVar, outputIndexVar])
  refine ⟨final, 2 + (2 + (loopCost + 1)), ?_, ?_, finalIndex,
    finalInvariant.array, ?_⟩
  · exact BigStep.seq hrunCard (BigStep.seq hrunIndex
      (BigStep.seq loopRun BigStep.skip))
  · simpa [finalIndex] using finalInvariant.card
  · omega

/-- A fixed exponent is compiled into a straight-line multiplication tree. -/
def natPowExpr (base : Expr) : ℕ → Expr
  | 0 => .lit 1
  | exponent + 1 => .mul (natPowExpr base exponent) base

lemma natPowExpr_eval (base : Expr) (state : Env) (exponent value : ℕ)
    (hbase : base.eval state = some value) :
    (natPowExpr base exponent).eval state = some (value ^ exponent) := by
  induction exponent with
  | zero => simp [natPowExpr, Expr.eval]
  | succ exponent ih =>
      simp [natPowExpr, Expr.eval, ih, hbase, Nat.pow_succ]

@[simp] lemma natPowExpr_size (base : Expr) (exponent : ℕ) :
    (natPowExpr base exponent).size = exponent * (base.size + 1) + 1 := by
  induction exponent with
  | zero => simp [natPowExpr, Expr.size]
  | succ exponent ih =>
      simp [natPowExpr, Expr.size, ih]
      ring

/-- Write the rational Håstad-gap decision bit. -/
def writeGapDecision (q : ℕ) : Com :=
  Com.block [
    .assign decisionLeftVar (natPowExpr (.var orderVar) (q + 3)),
    .assign decisionRightVar (natPowExpr (.var outputCardVar) q),
    .ite (.lt (.var decisionRightVar) (.var decisionLeftVar))
      (.write (.lit 0)) (.write (.lit 1))]

theorem writeGapDecision_bigStep (q : ℕ) (n card : ℕ) (initial : Env)
    (horder : initial.vars orderVar = n)
    (hcard : initial.vars outputCardVar = card)
    (hout : initial.out = []) :
    ∃ final cost,
      BigStep (writeGapDecision q) initial final cost ∧
      final.out = (if n ^ (q + 3) ≤ card ^ q then [1] else [0]) ∧
      cost ≤ 10 * (q + 5) := by
  let left := n ^ (q + 3)
  let right := card ^ q
  let afterLeft := initial.setVar decisionLeftVar left
  let afterRight := afterLeft.setVar decisionRightVar right
  have hleftEval :
      (natPowExpr (.var orderVar) (q + 3)).eval initial = some left := by
    apply natPowExpr_eval
    simpa [Expr.eval, horder]
  have hrightBase : (Expr.var outputCardVar).eval afterLeft = some card := by
    have hne : outputCardVar ≠ decisionLeftVar := by decide
    simpa [Expr.eval, afterLeft, Env.setVar, hne] using hcard
  have hrightEval :
      (natPowExpr (.var outputCardVar) q).eval afterLeft = some right := by
    exact natPowExpr_eval _ _ _ _ hrightBase
  have runLeft : BigStep
      (.assign decisionLeftVar (natPowExpr (.var orderVar) (q + 3)))
      initial afterLeft (1 + ((q + 3) * 2 + 1)) := by
    simpa [afterLeft, Expr.size] using BigStep.assign hleftEval
  have runRight : BigStep
      (.assign decisionRightVar (natPowExpr (.var outputCardVar) q))
      afterLeft afterRight (1 + (q * 2 + 1)) := by
    simpa [afterRight, Expr.size] using BigStep.assign hrightEval
  have hleftVar : afterRight.vars decisionLeftVar = left := by
    simp [afterRight, afterLeft, Env.setVar, decisionLeftVar, decisionRightVar]
  have hrightVar : afterRight.vars decisionRightVar = right := by
    simp [afterRight, Env.setVar]
  by_cases haccept : left ≤ right
  · let final := { afterRight with out := afterRight.out ++ [1] }
    have hcondition :
        (Cond.lt (.var decisionRightVar) (.var decisionLeftVar)).eval
          afterRight = some false := by
      simp [Cond.eval, hleftVar, hrightVar]
      omega
    have runBranch : BigStep
        (.ite (.lt (.var decisionRightVar) (.var decisionLeftVar))
          (.write (.lit 0)) (.write (.lit 1))) afterRight final 6 := by
      exact BigStep.ite_false hcondition (BigStep.write rfl)
    refine ⟨final, (1 + ((q + 3) * 2 + 1)) +
      ((1 + (q * 2 + 1)) + (6 + 1)),
      ?_, ?_, by omega⟩
    · exact BigStep.seq runLeft (BigStep.seq runRight
        (BigStep.seq runBranch BigStep.skip))
    · simp [final, afterRight, afterLeft, Env.setVar, hout, left, right,
        haccept]
  · let final := { afterRight with out := afterRight.out ++ [0] }
    have hcondition :
        (Cond.lt (.var decisionRightVar) (.var decisionLeftVar)).eval
          afterRight = some true := by
      simp [Cond.eval, hleftVar, hrightVar]
      omega
    have runBranch : BigStep
        (.ite (.lt (.var decisionRightVar) (.var decisionLeftVar))
          (.write (.lit 0)) (.write (.lit 1))) afterRight final 6 := by
      exact BigStep.ite_true hcondition (BigStep.write rfl)
    refine ⟨final, (1 + ((q + 3) * 2 + 1)) +
      ((1 + (q * 2 + 1)) + (6 + 1)),
      ?_, ?_, by omega⟩
    · exact BigStep.seq runLeft (BigStep.seq runRight
        (BigStep.seq runBranch BigStep.skip))
    · simp [final, afterRight, afterLeft, Env.setVar, hout, left, right,
        haccept]

/-! ### The supplied finite Turing machine as native IMP+ -/

noncomputable def approximationWitness {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) :
    Turing.TM2ComputableInPolyTime encode encode algorithm.program.function :=
  Classical.choice algorithm.program.polytime

open Lax51Proofs.TMToRam in
noncomputable def approximationNativeCom {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : Com :=
  let H := approximationWitness algorithm
  let tm := H.tm
  let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
  let outputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₁
  let separatorIn := FinTM2.inputSymbolCode tm H.inputAlphabet .separator
  let zeroIn := FinTM2.inputSymbolCode tm H.inputAlphabet .zero
  let oneIn := FinTM2.inputSymbolCode tm H.inputAlphabet .one
  let separatorOut := FinTM2.outputSymbolCode tm H.outputAlphabet .separator
  let zeroOut := FinTM2.outputSymbolCode tm H.outputAlphabet .zero
  let oneOut := FinTM2.outputSymbolCode tm H.outputAlphabet .one
  let initialStateCode :=
    @finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState
  let mainLabelCode :=
    @finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main
  FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
    separatorOut zeroOut oneOut initialStateCode mainLabelCode

open Lax51Proofs.TMToRam in
noncomputable def approximationNativeCost {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε)
    (input output : BitString) : ℕ :=
  let H := approximationWitness algorithm
  let tm := H.tm
  (encodeInputLoopCost input + 19 * bitSize input + 18) +
    (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
      (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
        maxCost (FinTM2.compileDispatcher tm 0).com) *
          H.time.eval (bitSize input) +
      (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
    (29 * bitSize output + 19) + 1

theorem approximationNativeCom_bigStep {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString) :
    ∃ ext final cost,
      BigStep (approximationNativeCom algorithm)
        (initEnv ext (input.length :: input)) final cost ∧
      final.out = algorithm.program.output input ∧
      cost ≤ approximationNativeCost algorithm input
        (algorithm.program.output input) := by
  let H := approximationWitness algorithm
  have hrun := H.outputsFun input
  obtain ⟨ext, final, cost, bounded, hcost, hout⟩ :=
    Lax51Proofs.TMToRam.FinTM2.compileNativeMachine_outputsInTime_bounded
      H.tm H.inputAlphabet H.outputAlphabet input
      (algorithm.program.output input) (H.time.eval (bitSize input)) hrun
  refine ⟨ext, final, cost, ?_, hout, ?_⟩
  · simpa [approximationNativeCom, H] using bounded.bigStep
  · simpa [approximationNativeCost, H] using hcost

@[simp] lemma algorithmName_ne_of_head_r (name target : String)
    (htarget : target.toList.head? = some 'r') :
    algorithmName name ≠ target := by
  intro equality
  have heads := congrArg (fun value : String => value.toList.head?) equality
  simp [algorithmName, algorithmPrefix, htarget] at heads

lemma algorithmName_not_mem_reduction_wvars (name : String) :
    algorithmName name ∉ reductionCom.wvars := by
  have heads : ∀ target ∈ reductionCom.wvars,
      target.toList.head? = some 'r' := by
    set_option maxRecDepth 100000 in
      decide
  intro membership
  exact (algorithmName_ne_of_head_r name _ (heads _ membership)) rfl

lemma algorithmName_not_mem_reduction_warrs (name : String) :
    algorithmName name ∉ reductionCom.warrs := by
  have heads : ∀ target ∈ reductionCom.warrs,
      target.toList.head? = some 'r' := by
    set_option maxRecDepth 100000 in
      decide
  intro membership
  exact (algorithmName_ne_of_head_r name _ (heads _ membership)) rfl

/-- Array sizes used by the composed IMP+ run. -/
def combinedExt (sourceExt : String → ℕ) (input : BitString)
    (countLength graphLength outputCapacity : ℕ) : String → ℕ :=
  fun name =>
    if name = rawArray then input.length
    else if name = countsArray then countLength
    else if name = graphArray then graphLength
    else if name = algorithmOutputArray then outputCapacity
    else sourceExt
      (String.ofList (name.toList.drop algorithmPrefix.toList.length))

lemma combinedExt_algorithmName (sourceExt : String → ℕ) (input : BitString)
    (countLength graphLength outputCapacity : ℕ) (name : String) :
    combinedExt sourceExt input countLength graphLength outputCapacity
        (algorithmName name) = sourceExt name := by
  have hraw : algorithmName name ≠ rawArray :=
    algorithmName_ne_of_head_r name rawArray (by decide)
  have hcounts : algorithmName name ≠ countsArray :=
    algorithmName_ne_of_head_r name countsArray (by decide)
  have hgraph : algorithmName name ≠ graphArray :=
    algorithmName_ne_of_head_r name graphArray (by decide)
  have houtput : algorithmName name ≠ algorithmOutputArray :=
    algorithmName_ne_of_head_r name algorithmOutputArray (by decide)
  simp only [combinedExt, hraw, hcounts, hgraph, houtput, ↓reduceIte]
  simp [algorithmName, algorithmPrefix]

@[simp] lemma combinedExt_raw (sourceExt : String → ℕ) (input : BitString)
    (countLength graphLength outputCapacity : ℕ) :
    combinedExt sourceExt input countLength graphLength outputCapacity rawArray =
      input.length := by
  simp [combinedExt]

@[simp] lemma combinedExt_counts (sourceExt : String → ℕ) (input : BitString)
    (countLength graphLength outputCapacity : ℕ) :
    combinedExt sourceExt input countLength graphLength outputCapacity countsArray =
      countLength := by
  simp [combinedExt, show countsArray ≠ rawArray by decide]

@[simp] lemma combinedExt_graph (sourceExt : String → ℕ) (input : BitString)
    (countLength graphLength outputCapacity : ℕ) :
    combinedExt sourceExt input countLength graphLength outputCapacity graphArray =
      graphLength := by
  simp [combinedExt, show graphArray ≠ rawArray by decide,
    show graphArray ≠ countsArray by decide]

@[simp] lemma combinedExt_output (sourceExt : String → ℕ) (input : BitString)
    (countLength graphLength outputCapacity : ℕ) :
    combinedExt sourceExt input countLength graphLength outputCapacity
        algorithmOutputArray = outputCapacity := by
  simp [combinedExt, show algorithmOutputArray ≠ rawArray by decide,
    show algorithmOutputArray ≠ countsArray by decide,
    show algorithmOutputArray ≠ graphArray by decide]

/-- The nonzero-order branch: reduce, run the approximation machine, count,
and decide. -/
noncomputable def positiveGapCom (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : Com :=
  Com.block [
    reductionAfterDecode,
    redirectCom (approximationNativeCom algorithm),
    countAlgorithmOutput,
    writeGapDecision q]

/-- A total command on all finite words.  The zero-order branch returns
false; every canonical graph input used by the gap theorem has positive
order. -/
noncomputable def gapCom (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : Com :=
  .seq inputPrelude <| .seq decodeOrder <|
    .ite (.eq (.var orderVar) (.lit 0))
      (.write (.lit 0)) (positiveGapCom q algorithm)

end Lax47Proofs.GapMachine
