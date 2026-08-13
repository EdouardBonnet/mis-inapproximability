import Lax47Proofs.RamReductionTriangle

/-!
The first-violation scan for the fixed IMP+ reduction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionSemantics

open Lax47.Machine Lax47.Complexity Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

/-! ### First-violation scan -/

def executionSelectionPrefix {n : ℕ} (graph : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ)
    (prefixLength : ℕ) : Option (ExecutionTriple n) :=
  (scanExecutionTriples graph seed counts
    ((executionTriples n).take prefixLength)).1

lemma scanExecutionTriples_append_fst {n : ℕ} (graph : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ)
    (first second : List (ExecutionTriple n)) :
    (scanExecutionTriples graph seed counts (first ++ second)).1 =
      match (scanExecutionTriples graph seed counts first).1 with
      | some triple => some triple
      | none => (scanExecutionTriples graph seed counts second).1 := by
  induction first with
  | nil => simp [scanExecutionTriples]
  | cons triple rest ih =>
      simp only [List.cons_append, scanExecutionTriples]
      by_cases hviolates : executionViolates graph seed counts triple <;>
        simp [hviolates, ih, scanExecutionTriples]

@[simp] lemma executionSelectionPrefix_zero {n : ℕ} (graph : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ) :
    executionSelectionPrefix graph seed counts 0 = none := by
  simp [executionSelectionPrefix, scanExecutionTriples]

lemma executionSelectionPrefix_succ {n rank : ℕ} (graph : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ)
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    executionSelectionPrefix graph seed counts (rank + 1) =
      match executionSelectionPrefix graph seed counts rank with
      | some triple => some triple
      | none =>
          if executionViolates graph seed counts (tripleAtRank n rank hrank) then
            some (tripleAtRank n rank hrank)
          else none := by
  rw [executionSelectionPrefix, List.take_add_one,
    scanExecutionTriples_append_fst]
  have hindex : rank < (executionTriples n).length := by simpa using hrank
  rw [List.getElem?_eq_getElem hindex]
  rw [executionTriples_getElem hrank]
  simp only [Option.toList_some]
  simp [scanExecutionTriples, executionSelectionPrefix, tripleAtRank]
  split <;> simp_all
  all_goals split <;> rfl

/-- The three selected edge registers encode the pure scan result. -/
def SelectionRepresent {n : ℕ} (selection : Option (ExecutionTriple n))
    (state : Env) : Prop :=
  match selection with
  | none => state.vars foundVar = 0
  | some triple =>
      state.vars foundVar = 1 ∧
      state.vars selectedEdgeOneVar =
        edgeSlot s(executionFirstVertex triple, executionSecondVertex triple) ∧
      state.vars selectedEdgeTwoVar =
        edgeSlot s(executionFirstVertex triple, executionThirdVertex triple) ∧
      state.vars selectedEdgeThreeVar =
        edgeSlot s(executionSecondVertex triple, executionThirdVertex triple)

def ScanInvariant {n : ℕ} (graph : GraphCode n) (seed : ExecutionSeed n)
    (counts : EdgeVariable n → ℕ) (input : BitString) (state : Env) : Prop :=
  ExecutionContext n input counts state ∧
  state.vars rankVar ≤ (n * n) * (n * n) * (n * n) ∧
  SelectionRepresent
    (executionSelectionPrefix graph seed counts (state.vars rankVar)) state

/-- Saving a decoded triple changes only the five selection registers. -/
theorem rememberCurrentTriple_spec (B : ℕ) {n rank : ℕ}
    (input : BitString) (counts : EdgeVariable n → ℕ)
    (hrank : rank < (n * n) * (n * n) * (n * n))
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hcountLenB : (n * n) * (n * n) < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        HasDecodedTriple n rank state ∧ state.vars rankVar = rank)
      rememberCurrentTriple
      (fun _ final => ExecutionContext n input counts final ∧
        final.vars rankVar = rank ∧
        SelectionRepresent (some (tripleAtRank n rank hrank)) final)
      30 := by
  have hedgeB (edge : EdgeVariable n) : edgeSlot edge < B :=
    (edgeSlot_lt edge).trans hcountLenB
  unfold Spec rememberCurrentTriple Com.block setOne
  intro state hstate
  run_vcg
  all_goals
    simp_all [SelectionRepresent, ExecutionContext, HasRawInput,
      HasParameters, CountsRepresent, HasDecodedTriple, HasDecodedRanks,
      Env.setVar, decodedEdgeOne_eq hrank, decodedEdgeTwo_eq hrank,
      decodedEdgeThree_eq hrank, rawLenVar, orderVar, blowupVar,
      countLenVar, tripleLenVar, budgetVar, sampleTargetVar, sampleBitsVar,
      foundVar, selectedVar, selectedEdgeOneVar, selectedEdgeTwoVar,
      selectedEdgeThreeVar, firstVar, secondVar, thirdVar, firstBaseVar,
      secondBaseVar, thirdBaseVar, edgeOneVar, edgeTwoVar, edgeThreeVar,
      rankVar, countsArray, rawArray]
  all_goals omega

/-- Incrementing the scan rank preserves the execution context and selection. -/
theorem incrementRank_spec (B : ℕ) {n rank : ℕ}
    (input : BitString) (counts : EdgeVariable n → ℕ)
    (selection : Option (ExecutionTriple n)) (hnextB : rank + 1 < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        state.vars rankVar = rank ∧ SelectionRepresent selection state)
      (increment rankVar)
      (fun _ final => ExecutionContext n input counts final ∧
        final.vars rankVar = rank + 1 ∧ SelectionRepresent selection final)
      4 := by
  unfold Spec increment
  intro state hstate
  run_vcg
  cases selection <;>
    simp_all [SelectionRepresent, ExecutionContext, HasRawInput,
      HasParameters, CountsRepresent, Env.setVar, rawLenVar, orderVar,
      blowupVar, countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
      sampleBitsVar, foundVar, selectedEdgeOneVar, selectedEdgeTwoVar,
      selectedEdgeThreeVar, rankVar, countsArray, rawArray]

theorem scanTriplesBody_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let seed := executionSeedOfFlat flatSeed
    let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
    Spec B
      (fun state => ScanInvariant graph seed counts input state ∧
        state.vars rankVar < (n * n) * (n * n) * (n * n))
      scanTriplesBody
      (fun initial final => ScanInvariant graph seed counts input final ∧
        final.vars rankVar = initial.vars rankVar + 1)
      (testCost + 200) := by
  dsimp only
  let seed := executionSeedOfFlat flatSeed
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  unfold Spec
  intro initial hstate
  rcases hstate with ⟨hinvariant, hrank⟩
  rcases hinvariant with ⟨hcontext, _hrankLe, hrepresent⟩
  let rank := initial.vars rankVar
  have htest := testCurrentTriple_spec B input graph flatSeed model counts hn hrank hB
    htripleB hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
  cases hselection : executionSelectionPrefix graph seed counts rank with
  | none =>
      have hfound : initial.vars foundVar = 0 := by
        simpa [SelectionRepresent, rank, seed, hselection] using hrepresent
      cases hviolates : executionViolates graph seed counts
        (tripleAtRank n rank hrank)
      · have htestCase :
            Spec B
              (fun state => ExecutionContext n input counts state ∧
                state.vars rankVar = rank ∧ state.vars foundVar = 0)
              testCurrentTriple
              (fun _ final => ExecutionContext n input counts final ∧
                HasDecodedTriple n rank final ∧ final.vars okVar = 0 ∧
                final.vars rankVar = rank ∧ final.vars foundVar = 0)
              testCost := by
          have htestFrame := htest.frame
          apply htestFrame.conseq
          · intro _ hpre
            simpa [rank] using ⟨hpre.1, hpre.2.1⟩
          · intro _ _ hpre hpost
            rcases hpost with ⟨hpost, hvars, _harrs, _hinp, _hout⟩
            refine ⟨hpost.1, hpost.2.1, ?_, ?_, ?_⟩
            · simpa [seed, rank, hviolates, bitWord] using hpost.2.2
            · exact (hvars rankVar (by decide)).trans hpre.2.1
            · exact (hvars foundVar (by decide)).trans hpre.2.2
          · rfl
        obtain ⟨tested, hrunTest, htestedContext, _hdecoded, hok,
          htestedRank, htestedFound⟩ :=
          htestCase.run ⟨hcontext, rfl, hfound⟩
        have hfoundCond :
            (Cond.eq (.var foundVar) (.lit 0)).evalB B initial = some true :=
          (evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))).trans
            (by simp [hfound])
        have hokCond :
            (Cond.eq (.var okVar) (.lit 1)).evalB B tested = some false :=
          (evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))).trans
            (by simp [hok])
        have hinnerRun :=
          Run.ite_false (c := rememberCurrentTriple) hokCond Run.skip
        have hthenRun := Run.seq hrunTest (Run.seq hinnerRun Run.skip)
        have houterRun := Run.ite_true (d := .skip) hfoundCond hthenRun
        have hnextB : rank + 1 < B := by omega
        obtain ⟨final, hrunIncrement, hfinalContext, hfinalRank,
          hfinalSelection⟩ :=
          (incrementRank_spec B input counts none hnextB).run
            ⟨htestedContext, htestedRank,
              by simpa [SelectionRepresent] using htestedFound⟩
        have hbodyRun :=
          Run.seq houterRun (Run.seq hrunIncrement Run.skip)
        have hnextSelection :
            executionSelectionPrefix graph seed counts (rank + 1) = none := by
          simpa [rank, hselection, hviolates] using
            (executionSelectionPrefix_succ graph seed counts hrank)
        have hfinalPrefix :
            SelectionRepresent
              (executionSelectionPrefix graph seed counts
                (final.vars rankVar)) final := by
          rw [hfinalRank, hnextSelection]
          exact hfinalSelection
        refine ⟨final, ?_, ?_⟩
        · simpa [scanTriplesBody] using
            (hbodyRun.mono (K' := testCost + 200) (by simp <;> omega))
        · refine ⟨⟨hfinalContext, ?_, hfinalPrefix⟩, ?_⟩
          · omega
          · simpa [rank] using hfinalRank
      · have htestCase :
            Spec B
              (fun state => ExecutionContext n input counts state ∧
                state.vars rankVar = rank ∧ state.vars foundVar = 0)
              testCurrentTriple
              (fun _ final => ExecutionContext n input counts final ∧
                HasDecodedTriple n rank final ∧ final.vars okVar = 1 ∧
                final.vars rankVar = rank ∧ final.vars foundVar = 0)
              testCost := by
          have htestFrame := htest.frame
          apply htestFrame.conseq
          · intro _ hpre
            simpa [rank] using ⟨hpre.1, hpre.2.1⟩
          · intro _ _ hpre hpost
            rcases hpost with ⟨hpost, hvars, _harrs, _hinp, _hout⟩
            refine ⟨hpost.1, hpost.2.1, ?_, ?_, ?_⟩
            · simpa [seed, rank, hviolates, bitWord] using hpost.2.2
            · exact (hvars rankVar (by decide)).trans hpre.2.1
            · exact (hvars foundVar (by decide)).trans hpre.2.2
          · rfl
        obtain ⟨tested, hrunTest, htestedContext, hdecoded, hok,
          htestedRank, _htestedFound⟩ :=
          htestCase.run ⟨hcontext, rfl, hfound⟩
        have hfoundCond :
            (Cond.eq (.var foundVar) (.lit 0)).evalB B initial = some true :=
          (evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))).trans
            (by simp [hfound])
        have hokCond :
            (Cond.eq (.var okVar) (.lit 1)).evalB B tested = some true :=
          (evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))).trans
            (by simp [hok])
        obtain ⟨remembered, hrunRemember, hrememberedContext,
          hrememberedRank, hrememberedSelection⟩ :=
          (rememberCurrentTriple_spec B input counts hrank htripleB
            hcountLenB).run ⟨htestedContext, hdecoded, htestedRank⟩
        have hinnerRun :=
          Run.ite_true (d := .skip) hokCond hrunRemember
        have hthenRun := Run.seq hrunTest (Run.seq hinnerRun Run.skip)
        have houterRun := Run.ite_true (d := .skip) hfoundCond hthenRun
        have hnextB : rank + 1 < B := by omega
        obtain ⟨final, hrunIncrement, hfinalContext, hfinalRank,
          hfinalSelection⟩ :=
          (incrementRank_spec B input counts
            (some (tripleAtRank n rank hrank)) hnextB).run
              ⟨hrememberedContext, hrememberedRank,
                hrememberedSelection⟩
        have hbodyRun :=
          Run.seq houterRun (Run.seq hrunIncrement Run.skip)
        have hnextSelection :
            executionSelectionPrefix graph seed counts (rank + 1) =
              some (tripleAtRank n rank hrank) := by
          simpa [rank, hselection, hviolates] using
            (executionSelectionPrefix_succ graph seed counts hrank)
        have hfinalPrefix :
            SelectionRepresent
              (executionSelectionPrefix graph seed counts
                (final.vars rankVar)) final := by
          rw [hfinalRank, hnextSelection]
          exact hfinalSelection
        refine ⟨final, ?_, ?_⟩
        · simpa [scanTriplesBody] using
            (hbodyRun.mono (K' := testCost + 200) (by simp <;> omega))
        · refine ⟨⟨hfinalContext, ?_, hfinalPrefix⟩, ?_⟩
          · omega
          · simpa [rank] using hfinalRank
  | some selected =>
      have hinitialSelection : SelectionRepresent (some selected) initial := by
        simpa [rank, seed, hselection] using hrepresent
      have hfound : initial.vars foundVar = 1 := hinitialSelection.1
      have hfoundCond :
          (Cond.eq (.var foundVar) (.lit 0)).evalB B initial = some false :=
        (evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))).trans
          (by simp [hfound])
      have houterRun := Run.ite_false
        (c := Com.block [testCurrentTriple,
          .ite (.eq (.var okVar) (.lit 1)) rememberCurrentTriple .skip])
        hfoundCond Run.skip
      have hnextB : rank + 1 < B := by omega
      obtain ⟨final, hrunIncrement, hfinalContext, hfinalRank,
        hfinalSelection⟩ :=
        (incrementRank_spec B input counts (some selected) hnextB).run
          ⟨hcontext, rfl, hinitialSelection⟩
      have hbodyRun := Run.seq houterRun (Run.seq hrunIncrement Run.skip)
      have hnextSelection :
          executionSelectionPrefix graph seed counts (rank + 1) =
            some selected := by
        simpa [rank, hselection] using
          (executionSelectionPrefix_succ graph seed counts hrank)
      have hfinalPrefix :
          SelectionRepresent
            (executionSelectionPrefix graph seed counts
              (final.vars rankVar)) final := by
        rw [hfinalRank, hnextSelection]
        exact hfinalSelection
      refine ⟨final, ?_, ?_⟩
      · simpa [scanTriplesBody] using
          (hbodyRun.mono (K' := testCost + 200) (by simp <;> omega))
      · refine ⟨⟨hfinalContext, ?_, hfinalPrefix⟩, ?_⟩
        · omega
        · simpa [rank] using hfinalRank

lemma executionSelectionPrefix_full {n : ℕ} (graph : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ) :
    executionSelectionPrefix graph seed counts
      ((n * n) * (n * n) * (n * n)) =
      (findExecutionViolation graph seed counts).1 := by
  have hlength :
      (n * n) * (n * n) * (n * n) = (executionTriples n).length := by
    simp
  have htake :
      (executionTriples n).take ((n * n) * (n * n) * (n * n)) =
        executionTriples n := by
    apply (List.take_eq_self_iff _).2
    exact hlength.symm.le
  simp [executionSelectionPrefix, findExecutionViolation, htake]

theorem scanTriples_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let seed := executionSeedOfFlat flatSeed
    let tripleCount := (n * n) * (n * n) * (n * n)
    let bodyCost :=
      (2000 + 3 * ((200 + 4) * executionSampleBits n + 100)) + 200
    let scanCost := (bodyCost + 4) * tripleCount + 100
    Spec B
      (ExecutionContext n input counts)
      scanTriples
      (fun _ final =>
        ExecutionContext n input counts final ∧
        final.vars rankVar = tripleCount ∧
        SelectionRepresent (findExecutionViolation graph seed counts).1 final)
      scanCost := by
  dsimp only
  let seed := executionSeedOfFlat flatSeed
  let tripleCount := (n * n) * (n * n) * (n * n)
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  let bodyCost := testCost + 200
  let scanCost := (bodyCost + 4) * tripleCount + 100
  let invariant := ScanInvariant graph seed counts input
  have hbodyBase := scanTriplesBody_spec B input graph flatSeed model counts hn hB
    htripleB hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
  have hbody :
      Spec B (fun state => invariant state ∧ state.vars rankVar < tripleCount)
        scanTriplesBody
        (fun initial final => invariant final ∧
          final.vars rankVar = initial.vars rankVar + 1)
        bodyCost := by
    simpa only [seed, tripleCount, testCost, bodyCost] using hbodyBase
  have hloop := Spec.forRangeZero rankVar tripleLenVar invariant
    tripleCount bodyCost (by dsimp [tripleCount]; omega)
    (fun _ hstate => hstate.2.1)
    (fun _ hstate => by
      simpa only [invariant, ScanInvariant, tripleCount] using
        hstate.1.2.1.2.2.2.1)
    hbody
  unfold Spec
  intro initial hinitial
  let afterFound := initial.setVar foundVar 0
  let prepared := afterFound.setVar selectedVar 0
  have hrunFound :
      Run B (setZero foundVar) initial afterFound 2 := by
    exact Run.assign (evalB_lit (by omega))
  have hrunSelected :
      Run B (setZero selectedVar) afterFound prepared 2 := by
    exact Run.assign (evalB_lit (by omega))
  have hloopPre : invariant (prepared.setVar rankVar 0) := by
    simpa [invariant, ScanInvariant, SelectionRepresent,
      executionSelectionPrefix_zero, ExecutionContext, HasParameters,
      HasRawInput, CountsRepresent, prepared, afterFound, Env.setVar,
      foundVar, selectedVar, rankVar, orderVar, blowupVar,
      countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
      sampleBitsVar, rawLenVar, countsArray, rawArray] using hinitial
  obtain ⟨final, hrunLoop, hfinalInvariant, hfinalRank⟩ :=
    hloop.run hloopPre
  have hrunAll :=
    Run.seq hrunFound (Run.seq hrunSelected (Run.seq hrunLoop Run.skip))
  rcases hfinalInvariant with
    ⟨hfinalContext, _hfinalRankLe, hfinalSelection⟩
  have hfinalSelection' :
      SelectionRepresent (findExecutionViolation graph seed counts).1 final := by
    rw [← executionSelectionPrefix_full graph seed counts]
    simpa [hfinalRank, tripleCount] using hfinalSelection
  refine ⟨final, ?_, hfinalContext, hfinalRank, hfinalSelection'⟩
  simpa [scanTriples] using
    (hrunAll.mono (K' := scanCost) (by
      dsimp [scanCost]
      omega))
end Lax47Proofs.RamReductionSemantics
