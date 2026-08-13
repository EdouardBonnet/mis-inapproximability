import Lax47Proofs.RamReductionSemantics

/-!
Context-preserving semantic specifications and correctness of the complete
triangle predicate for the fixed IMP+ reduction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionSemantics

open Lax47.Machine Lax47.Complexity Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

/-! ### Context-preserving elementary tests -/

theorem requireGraphAdjacency_context_spec (B : ℕ) {n : ℕ}
    (input : BitString) (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ) (left right : Fin n)
    (leftName rightName : String) (initialOk : ℕ)
    (hnB : n < B)
    (hforward : 2 + left.1 * n + right.1 < B)
    (hbackward : 2 + right.1 * n + left.1 < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hleftSafe : leftName ≠ rawIndexVar ∧ leftName ≠ tempVar ∧
      leftName ≠ okVar)
    (hrightSafe : rightName ≠ rawIndexVar ∧ rightName ≠ tempVar ∧
      rightName ≠ okVar) :
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        state.vars leftName = left.1 ∧ state.vars rightName = right.1 ∧
        state.vars okVar = initialOk)
      (requireGraphAdjacency leftName rightName)
      (fun _ final =>
        ExecutionContext n input counts final ∧
        final.vars leftName = left.1 ∧ final.vars rightName = right.1 ∧
        final.vars okVar = retainIf initialOk (graph.adjacent left right))
      250 := by
  have hbase := requireGraphAdjacency_spec B n
    input left right leftName rightName initialOk
    hnB hforward hbackward hleftSafe hrightSafe
  have hframe := hbase.frame
  apply hframe.conseq
  · intro state hstate
    rcases hstate with ⟨hcontext, hleft, hright, hok⟩
    exact ⟨hcontext.1, hcontext.2.1.1, hleft, hright, hok,
      hinputB, hvaluesB, by omega⟩
  · intro initial final hpre hpost
    rcases hpre with ⟨hcontext, hleft, hright, _hok⟩
    rcases hpost with ⟨hok, hvars, harrs, _hinp, _hout⟩
    have hdecoded := model.graph_eq
    have hnotWritten (name : String) (hOk : name ≠ okVar)
        (hRawIndex : name ≠ rawIndexVar) (hTemp : name ≠ tempVar) :
        name ∉ (requireGraphAdjacency leftName rightName).wvars := by
      simp [requireGraphAdjacency, requireRawAdjacencyDirection,
        Com.block, readRawBit, setZero, setOne, Com.wvars,
        hOk, hRawIndex, hTemp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hcontext with ⟨hraw, hparameters, hsample, hcounts⟩
      rcases hparameters with
        ⟨horder, hblowup, hcountLen, htripleLen, hbudget, htarget⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · calc
            final.vars rawLenVar = initial.vars rawLenVar := by
              apply hvars
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.wvars,
                rawLenVar, rawIndexVar, tempVar, okVar]
            _ = input.length := hraw.1
        · calc
            final.arrs rawArray = initial.arrs rawArray := by
              apply harrs
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.warrs]
            _ = input := hraw.2
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact (hvars orderVar (hnotWritten _ (by decide)
            (by decide) (by decide))).trans horder
        · exact (hvars blowupVar (hnotWritten _ (by decide)
            (by decide) (by decide))).trans hblowup
        · exact (hvars countLenVar (hnotWritten _ (by decide)
            (by decide) (by decide))).trans hcountLen
        · exact (hvars tripleLenVar (hnotWritten _ (by decide)
            (by decide) (by decide))).trans htripleLen
        · exact (hvars budgetVar (hnotWritten _ (by decide)
            (by decide) (by decide))).trans hbudget
        · exact (hvars sampleTargetVar (hnotWritten _ (by decide)
            (by decide) (by decide))).trans htarget
      · exact (hvars sampleBitsVar (hnotWritten _ (by decide)
          (by decide) (by decide))).trans hsample
      · refine ⟨?_, ?_⟩
        · calc
            (final.arrs countsArray).length =
                (initial.arrs countsArray).length := by
              rw [harrs countsArray]
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.warrs]
            _ = (n * n) * (n * n) := hcounts.1
        · intro edge
          rw [harrs countsArray]
          · exact hcounts.2 edge
          · simp [requireGraphAdjacency, requireRawAdjacencyDirection,
              Com.block, readRawBit, setZero, setOne, Com.warrs]
    · exact (hvars leftName (hnotWritten _ hleftSafe.2.2
        hleftSafe.1 hleftSafe.2.1)).trans hleft
    · exact (hvars rightName (hnotWritten _ hrightSafe.2.2
        hrightSafe.1 hrightSafe.2.1)).trans hright
    · simpa [hdecoded] using hok
  · rfl

theorem decodeTriple_context_spec (B : ℕ) {n rank : ℕ}
    (input : BitString) (counts : EdgeVariable n → ℕ)
    (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n))
    (hB : (n * n) * (n * n) * (n * n) + 1 < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        state.vars rankVar = rank)
      decodeTriple
      (fun _ final => ExecutionContext n input counts final ∧
        HasDecodedTriple n rank final)
      400 := by
  have hbase := decodeTriple_spec B n rank hn hrank hB
  have hframe := hbase.frame
  apply hframe.conseq
  · intro state hstate
    exact ⟨hstate.1.2.1.1, hstate.1.2.1.2.1, hstate.2⟩
  · intro initial final hpre hpost
    rcases hpre with ⟨hcontext, _hrank⟩
    rcases hpost with ⟨hdecoded, hvars, harrs, _hinp, _hout⟩
    rcases hcontext with ⟨hraw, hparameters, hsample, hcounts⟩
    rcases hparameters with
      ⟨horder, hblowup, hcountLen, htripleLen, hbudget, htarget⟩
    refine ⟨?_, hdecoded⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact (hvars rawLenVar (by decide)).trans hraw.1
      · rw [harrs rawArray]
        · exact hraw.2
        · simp [decodeTriple, decodeTripleRanks, decodeTripleEdges,
            edgeSlotCom, Com.block, Com.warrs]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hvars orderVar (by decide)).trans horder
      · exact (hvars blowupVar (by decide)).trans hblowup
      · exact (hvars countLenVar (by decide)).trans hcountLen
      · exact (hvars tripleLenVar (by decide)).trans htripleLen
      · exact (hvars budgetVar (by decide)).trans hbudget
      · exact (hvars sampleTargetVar (by decide)).trans htarget
    · exact (hvars sampleBitsVar (by decide)).trans hsample
    · refine ⟨?_, ?_⟩
      · rw [harrs countsArray]
        · exact hcounts.1
        · simp [decodeTriple, decodeTripleRanks, decodeTripleEdges,
            edgeSlotCom, Com.block, Com.warrs]
      · intro edge
        rw [harrs countsArray]
        · exact hcounts.2 edge
        · simp [decodeTriple, decodeTripleRanks, decodeTripleEdges,
            edgeSlotCom, Com.block, Com.warrs]
  · rfl

theorem requireGraphAdjacency_decoded_spec (B : ℕ) {n rank : ℕ}
    (input : BitString) (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ) (left right : Fin n)
    (leftName rightName : String) (initialOk : ℕ)
    (hnB : n < B)
    (hforward : 2 + left.1 * n + right.1 < B)
    (hbackward : 2 + right.1 * n + left.1 < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hleftSafe : leftName ≠ rawIndexVar ∧ leftName ≠ tempVar ∧
      leftName ≠ okVar)
    (hrightSafe : rightName ≠ rawIndexVar ∧ rightName ≠ tempVar ∧
      rightName ≠ okVar) :
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        HasDecodedTriple n rank state ∧
        state.vars leftName = left.1 ∧ state.vars rightName = right.1 ∧
        state.vars okVar = initialOk)
      (requireGraphAdjacency leftName rightName)
      (fun _ final =>
        ExecutionContext n input counts final ∧
        HasDecodedTriple n rank final ∧
        final.vars okVar = retainIf initialOk (graph.adjacent left right))
      250 := by
  have hbase := requireGraphAdjacency_context_spec B input graph flatSeed model counts
    left right leftName rightName initialOk hnB hforward hbackward
    hinputB hvaluesB hleftSafe hrightSafe
  have hframe := hbase.frame
  apply hframe.conseq
  · intro state hstate
    exact ⟨hstate.1, hstate.2.2.1, hstate.2.2.2.1, hstate.2.2.2.2⟩
  · intro initial final hpre hpost
    rcases hpre with ⟨_hcontext, hdecoded, _hleft, _hright, _hok⟩
    rcases hpost with
      ⟨⟨hcontext, _hleft', _hright', hok⟩, hvars, _harrs, _hinp, _hout⟩
    have hnotWritten (name : String) (hOk : name ≠ okVar)
        (hRawIndex : name ≠ rawIndexVar) (hTemp : name ≠ tempVar) :
        name ∉ (requireGraphAdjacency leftName rightName).wvars := by
      simp [requireGraphAdjacency, requireRawAdjacencyDirection,
        Com.block, readRawBit, setZero, setOne, Com.wvars,
        hOk, hRawIndex, hTemp]
    have hkeep (name : String) (hOk : name ≠ okVar)
        (hRawIndex : name ≠ rawIndexVar) (hTemp : name ≠ tempVar) :
        final.vars name = initial.vars name :=
      hvars name (hnotWritten name hOk hRawIndex hTemp)
    refine ⟨hcontext, ?_, hok⟩
    simpa only [HasDecodedTriple, HasDecodedRanks,
      hkeep blowupVar (by decide) (by decide) (by decide),
      hkeep firstVar (by decide) (by decide) (by decide),
      hkeep secondVar (by decide) (by decide) (by decide),
      hkeep thirdVar (by decide) (by decide) (by decide),
      hkeep firstBaseVar (by decide) (by decide) (by decide),
      hkeep secondBaseVar (by decide) (by decide) (by decide),
      hkeep thirdBaseVar (by decide) (by decide) (by decide),
      hkeep edgeOneVar (by decide) (by decide) (by decide),
      hkeep edgeTwoVar (by decide) (by decide) (by decide),
      hkeep edgeThreeVar (by decide) (by decide) (by decide)] using hdecoded
  · rfl

theorem requireSampledEdge_decoded_spec (B : ℕ) {n rank : ℕ}
    (input : BitString) (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ) (edge : EdgeVariable n)
    (edgeName : String) (initialOk : ℕ)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B)
    (hedgeSafe : edgeName ≠ rowVar ∧ edgeName ≠ rawIndexVar ∧
      edgeName ≠ tempVar ∧ edgeName ≠ okVar ∧ edgeName ≠ bitVar) :
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        HasDecodedTriple n rank state ∧ state.vars edgeName = edgeSlot edge ∧
        state.vars okVar = initialOk)
      (requireSampledEdge edgeName)
      (fun _ final =>
        ExecutionContext n input counts final ∧
        HasDecodedTriple n rank final ∧
        final.vars okVar = retainIf initialOk
          (executionCell (executionSeedOfFlat flatSeed) edge (counts edge)))
      ((200 + 4) * executionSampleBits n + 100) := by
  have hbase := requireSampledEdge_spec B input graph flatSeed model counts edge edgeName
    initialOk hB hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
    hedgeSafe
  have hframe := hbase.frame
  apply hframe.conseq
  · intro state hstate
    exact ⟨hstate.1, hstate.2.2.1, hstate.2.2.2⟩
  · intro initial final hpre hpost
    rcases hpre with ⟨_hcontext, hdecoded, _hedge, _hok⟩
    rcases hpost with
      ⟨⟨hcontext, _hedge', hok⟩, hvars, _harrs, _hinp, _hout⟩
    have hnotWritten (name : String) (hRow : name ≠ rowVar)
        (hRawIndex : name ≠ rawIndexVar) (hTemp : name ≠ tempVar)
        (hOk : name ≠ okVar) (hBit : name ≠ bitVar) :
        name ∉ (requireSampledEdge edgeName).wvars := by
      simp [requireSampledEdge, sampleBlockLoop, sampleBitBody,
        readRawBit, Com.block, increment, setZero, setOne, Com.wvars,
        hRow, hRawIndex, hTemp, hOk, hBit]
    have hkeep (name : String) (hRow : name ≠ rowVar)
        (hRawIndex : name ≠ rawIndexVar) (hTemp : name ≠ tempVar)
        (hOk : name ≠ okVar) (hBit : name ≠ bitVar) :
        final.vars name = initial.vars name :=
      hvars name (hnotWritten name hRow hRawIndex hTemp hOk hBit)
    refine ⟨hcontext, ?_, hok⟩
    simpa only [HasDecodedTriple, HasDecodedRanks,
      hkeep blowupVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep firstVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep secondVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep thirdVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep firstBaseVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep secondBaseVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep thirdBaseVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep edgeOneVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep edgeTwoVar (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep edgeThreeVar (by decide) (by decide) (by decide) (by decide) (by decide)] using hdecoded
  · rfl

/-! ### The complete triangle predicate -/

theorem testCurrentTriple_spec (B : ℕ) {n rank : ℕ}
    (input : BitString) (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ)
    (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n))
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let triple := tripleAtRank n rank hrank
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        state.vars rankVar = rank)
      testCurrentTriple
      (fun _ final =>
        ExecutionContext n input counts final ∧
        HasDecodedTriple n rank final ∧
        final.vars okVar = bitWord
          (executionViolates graph (executionSeedOfFlat flatSeed) counts triple))
      (2000 + 3 * ((200 + 4) * executionSampleBits n + 100)) := by
  dsimp only
  let triple := tripleAtRank n rank hrank
  let first := executionFirstVertex triple
  let second := executionSecondVertex triple
  let third := executionThirdVertex triple
  let edgeOne : EdgeVariable n := s(first, second)
  let edgeTwo : EdgeVariable n := s(first, third)
  let edgeThree : EdgeVariable n := s(second, third)
  let firstAdj := graph.adjacent first.1 second.1
  let secondAdj := graph.adjacent first.1 third.1
  let thirdAdj := graph.adjacent second.1 third.1
  let afterFirstAdj := retainIf 1 firstAdj
  let afterSecondAdj := retainIf afterFirstAdj secondAdj
  let afterThirdAdj := retainIf afterSecondAdj thirdAdj
  let afterEdgeOne := retainIf afterThirdAdj
    (executionCell (executionSeedOfFlat flatSeed) edgeOne (counts edgeOne))
  let afterEdgeTwo := retainIf afterEdgeOne
    (executionCell (executionSeedOfFlat flatSeed) edgeTwo (counts edgeTwo))
  let afterEdgeThree := retainIf afterEdgeTwo
    (executionCell (executionSeedOfFlat flatSeed) edgeThree (counts edgeThree))
  have hnB : n < B := by
    have hn2 : n ≤ n * n := by nlinarith
    omega
  have adjacencyPositionB (left right : Fin n) :
      2 + left.1 * n + right.1 < B := by
    have hleft := left.2
    have hright := right.2
    have : left.1 * n + right.1 < n * n := by nlinarith
    omega
  have hdecode := decodeTriple_context_spec B
    input counts hn hrank htripleB
  have hadjOne := requireGraphAdjacency_decoded_spec (rank := rank) B input graph flatSeed model counts
    first.1 second.1 firstBaseVar secondBaseVar 1 hnB
    (adjacencyPositionB first.1 second.1)
    (adjacencyPositionB second.1 first.1) hinputB hvaluesB
    (by decide) (by decide)
  have hadjTwo := requireGraphAdjacency_decoded_spec (rank := rank) B input graph flatSeed model counts
    first.1 third.1 firstBaseVar thirdBaseVar afterFirstAdj hnB
    (adjacencyPositionB first.1 third.1)
    (adjacencyPositionB third.1 first.1) hinputB hvaluesB
    (by decide) (by decide)
  have hadjThree := requireGraphAdjacency_decoded_spec (rank := rank) B input graph flatSeed model counts
    second.1 third.1 secondBaseVar thirdBaseVar afterSecondAdj hnB
    (adjacencyPositionB second.1 third.1)
    (adjacencyPositionB third.1 second.1) hinputB hvaluesB
    (by decide) (by decide)
  have hedgeOne := requireSampledEdge_decoded_spec (rank := rank) B input graph flatSeed model counts
    edgeOne edgeOneVar afterThirdAdj hB hinputB hvaluesB hbudgetB
    hsampleB hcountLenB hcountsB (by decide)
  have hedgeTwo := requireSampledEdge_decoded_spec (rank := rank) B input graph flatSeed model counts
    edgeTwo edgeTwoVar afterEdgeOne hB hinputB hvaluesB hbudgetB
    hsampleB hcountLenB hcountsB (by decide)
  have hedgeThree := requireSampledEdge_decoded_spec (rank := rank) B input graph flatSeed model counts
    edgeThree edgeThreeVar afterEdgeTwo hB hinputB hvaluesB hbudgetB
    hsampleB hcountLenB hcountsB (by decide)
  let StateAt (value : ℕ) (state : Env) : Prop :=
    ExecutionContext n input counts state ∧
    HasDecodedTriple n rank state ∧ state.vars okVar = value
  have hfirstBase (state : Env) (hdecoded : HasDecodedTriple n rank state) :
      state.vars firstBaseVar = first.1.1 := by
    calc
      state.vars firstBaseVar = decodedFirstRank (n * n) rank / n :=
        hdecoded.1.2.2.2.2.1
      _ = (executionFirstVertex (tripleAtRank n rank hrank)).1.1 :=
        decodedFirstBase_eq hn hrank
      _ = first.1.1 := rfl
  have hsecondBase (state : Env) (hdecoded : HasDecodedTriple n rank state) :
      state.vars secondBaseVar = second.1.1 := by
    calc
      state.vars secondBaseVar = decodedSecondRank (n * n) rank / n :=
        hdecoded.1.2.2.2.2.2.1
      _ = (executionSecondVertex (tripleAtRank n rank hrank)).1.1 :=
        decodedSecondBase_eq hn hrank
      _ = second.1.1 := rfl
  have hthirdBase (state : Env) (hdecoded : HasDecodedTriple n rank state) :
      state.vars thirdBaseVar = third.1.1 := by
    calc
      state.vars thirdBaseVar = decodedThirdRank (n * n) rank / n :=
        hdecoded.1.2.2.2.2.2.2
      _ = (executionThirdVertex (tripleAtRank n rank hrank)).1.1 :=
        decodedThirdBase_eq hn hrank
      _ = third.1.1 := rfl
  have hedgeOneValue (state : Env)
      (hdecoded : HasDecodedTriple n rank state) :
      state.vars edgeOneVar = edgeSlot edgeOne := by
    calc
      state.vars edgeOneVar = canonicalSlot (n * n)
          (decodedFirstRank (n * n) rank)
          (decodedSecondRank (n * n) rank) := hdecoded.2.1
      _ = edgeSlot s(executionFirstVertex (tripleAtRank n rank hrank),
          executionSecondVertex (tripleAtRank n rank hrank)) :=
        decodedEdgeOne_eq hrank
      _ = edgeSlot edgeOne := rfl
  have hedgeTwoValue (state : Env)
      (hdecoded : HasDecodedTriple n rank state) :
      state.vars edgeTwoVar = edgeSlot edgeTwo := by
    calc
      state.vars edgeTwoVar = canonicalSlot (n * n)
          (decodedFirstRank (n * n) rank)
          (decodedThirdRank (n * n) rank) := hdecoded.2.2.1
      _ = edgeSlot s(executionFirstVertex (tripleAtRank n rank hrank),
          executionThirdVertex (tripleAtRank n rank hrank)) :=
        decodedEdgeTwo_eq hrank
      _ = edgeSlot edgeTwo := rfl
  have hedgeThreeValue (state : Env)
      (hdecoded : HasDecodedTriple n rank state) :
      state.vars edgeThreeVar = edgeSlot edgeThree := by
    calc
      state.vars edgeThreeVar = canonicalSlot (n * n)
          (decodedSecondRank (n * n) rank)
          (decodedThirdRank (n * n) rank) := hdecoded.2.2.2
      _ = edgeSlot s(executionSecondVertex (tripleAtRank n rank hrank),
          executionThirdVertex (tripleAtRank n rank hrank)) :=
        decodedEdgeThree_eq hrank
      _ = edgeSlot edgeThree := rfl
  have hOneB : 1 < B := by omega
  have hsetOne :
      Spec B
        (fun state =>
          ExecutionContext n input counts state ∧
          HasDecodedTriple n rank state)
        (setOne okVar) (fun _ final => StateAt 1 final) 2 := by
    unfold Spec setOne
    intro state hstate
    refine ⟨state.setVar okVar 1, Run.assign (evalB_lit hOneB), ?_⟩
    rcases hstate with ⟨hcontext, hdecoded⟩
    simpa [StateAt, ExecutionContext, HasRawInput, HasParameters,
      CountsRepresent, HasDecodedTriple, HasDecodedRanks, Env.setVar,
      rawLenVar, orderVar, blowupVar, countLenVar, tripleLenVar,
      budgetVar, sampleTargetVar, sampleBitsVar, firstVar, secondVar,
      thirdVar, firstBaseVar, secondBaseVar, thirdBaseVar, edgeOneVar,
      edgeTwoVar, edgeThreeVar, okVar, countsArray, rawArray] using
        (show ExecutionContext n input counts state ∧
            HasDecodedTriple n rank state ∧ 1 = 1 from
          ⟨hcontext, hdecoded, rfl⟩)
  have hadjOne' :
      Spec B (StateAt 1) (requireGraphAdjacency firstBaseVar secondBaseVar)
        (fun _ final => StateAt afterFirstAdj final) 250 := by
    apply hadjOne.conseq
    · intro state hstate
      rcases hstate with ⟨hcontext, hdecoded, hok⟩
      exact ⟨hcontext, hdecoded, hfirstBase state hdecoded,
        hsecondBase state hdecoded, hok⟩
    · intro _ final _ hpost
      simpa [StateAt, afterFirstAdj] using hpost
    · rfl
  have hadjTwo' :
      Spec B (StateAt afterFirstAdj)
        (requireGraphAdjacency firstBaseVar thirdBaseVar)
        (fun _ final => StateAt afterSecondAdj final) 250 := by
    apply hadjTwo.conseq
    · intro state hstate
      rcases hstate with ⟨hcontext, hdecoded, hok⟩
      exact ⟨hcontext, hdecoded, hfirstBase state hdecoded,
        hthirdBase state hdecoded, hok⟩
    · intro _ final _ hpost
      simpa [StateAt, afterSecondAdj] using hpost
    · rfl
  have hadjThree' :
      Spec B (StateAt afterSecondAdj)
        (requireGraphAdjacency secondBaseVar thirdBaseVar)
        (fun _ final => StateAt afterThirdAdj final) 250 := by
    apply hadjThree.conseq
    · intro state hstate
      rcases hstate with ⟨hcontext, hdecoded, hok⟩
      exact ⟨hcontext, hdecoded, hsecondBase state hdecoded,
        hthirdBase state hdecoded, hok⟩
    · intro _ final _ hpost
      simpa [StateAt, afterThirdAdj] using hpost
    · rfl
  have hedgeOne' :
      Spec B (StateAt afterThirdAdj) (requireSampledEdge edgeOneVar)
        (fun _ final => StateAt afterEdgeOne final)
        ((200 + 4) * executionSampleBits n + 100) := by
    apply hedgeOne.conseq
    · intro state hstate
      rcases hstate with ⟨hcontext, hdecoded, hok⟩
      exact ⟨hcontext, hdecoded, hedgeOneValue state hdecoded, hok⟩
    · intro _ final _ hpost
      simpa [StateAt, afterEdgeOne] using hpost
    · rfl
  have hedgeTwo' :
      Spec B (StateAt afterEdgeOne) (requireSampledEdge edgeTwoVar)
        (fun _ final => StateAt afterEdgeTwo final)
        ((200 + 4) * executionSampleBits n + 100) := by
    apply hedgeTwo.conseq
    · intro state hstate
      rcases hstate with ⟨hcontext, hdecoded, hok⟩
      exact ⟨hcontext, hdecoded, hedgeTwoValue state hdecoded, hok⟩
    · intro _ final _ hpost
      simpa [StateAt, afterEdgeTwo] using hpost
    · rfl
  have hedgeThree' :
      Spec B (StateAt afterEdgeTwo) (requireSampledEdge edgeThreeVar)
        (fun _ final => StateAt afterEdgeThree final)
        ((200 + 4) * executionSampleBits n + 100) := by
    apply hedgeThree.conseq
    · intro state hstate
      rcases hstate with ⟨hcontext, hdecoded, hok⟩
      exact ⟨hcontext, hdecoded, hedgeThreeValue state hdecoded, hok⟩
    · intro _ final _ hpost
      simpa [StateAt, afterEdgeThree] using hpost
    · rfl
  have hafterFirst : afterFirstAdj = bitWord firstAdj := by
    exact retainIf_one firstAdj
  have hafterSecond :
      afterSecondAdj = bitWord (firstAdj && secondAdj) := by
    change retainIf afterFirstAdj secondAdj = _
    rw [hafterFirst, retainIf_bitWord]
  have hafterThird :
      afterThirdAdj = bitWord (firstAdj && secondAdj && thirdAdj) := by
    change retainIf afterSecondAdj thirdAdj = _
    rw [hafterSecond, retainIf_bitWord]
  have hafterEdgeOne :
      afterEdgeOne = bitWord (firstAdj && secondAdj && thirdAdj &&
        executionCell (executionSeedOfFlat flatSeed) edgeOne
          (counts edgeOne)) := by
    change retainIf afterThirdAdj
      (executionCell (executionSeedOfFlat flatSeed) edgeOne
        (counts edgeOne)) = _
    rw [hafterThird, retainIf_bitWord]
  have hafterEdgeTwo :
      afterEdgeTwo = bitWord (firstAdj && secondAdj && thirdAdj &&
        executionCell (executionSeedOfFlat flatSeed) edgeOne
          (counts edgeOne) &&
        executionCell (executionSeedOfFlat flatSeed) edgeTwo
          (counts edgeTwo)) := by
    change retainIf afterEdgeOne
      (executionCell (executionSeedOfFlat flatSeed) edgeTwo
        (counts edgeTwo)) = _
    rw [hafterEdgeOne, retainIf_bitWord]
  have hfinalValue : afterEdgeThree = bitWord
      (executionViolates graph (executionSeedOfFlat flatSeed) counts triple) := by
    change retainIf afterEdgeTwo
      (executionCell (executionSeedOfFlat flatSeed) edgeThree
        (counts edgeThree)) = _
    rw [hafterEdgeTwo, retainIf_bitWord]
    simp [executionViolates, executionBlowupAdjacent, firstAdj, secondAdj,
      thirdAdj, first, second, third, edgeOne, edgeTwo, edgeThree,
      triple, Bool.and_assoc]
  unfold Spec
  intro initial hinitial
  obtain ⟨afterDecode, runDecode, postDecode⟩ := hdecode.run hinitial
  obtain ⟨afterSet, runSet, postSet⟩ := hsetOne.run postDecode
  obtain ⟨afterAdjOne, runAdjOne, postAdjOne⟩ := hadjOne'.run postSet
  obtain ⟨afterAdjTwo, runAdjTwo, postAdjTwo⟩ := hadjTwo'.run postAdjOne
  obtain ⟨afterAdjThree, runAdjThree, postAdjThree⟩ :=
    hadjThree'.run postAdjTwo
  obtain ⟨afterSampleOne, runSampleOne, postSampleOne⟩ :=
    hedgeOne'.run postAdjThree
  obtain ⟨afterSampleTwo, runSampleTwo, postSampleTwo⟩ :=
    hedgeTwo'.run postSampleOne
  obtain ⟨final, runSampleThree, postFinal⟩ :=
    hedgeThree'.run postSampleTwo
  refine ⟨final, ?_, ?_⟩
  · unfold testCurrentTriple Com.block
    exact (runDecode.seq (runSet.seq (runAdjOne.seq (runAdjTwo.seq
      (runAdjThree.seq (runSampleOne.seq (runSampleTwo.seq
        (runSampleThree.seq Run.skip)))))))).mono (by omega)
  · rcases postFinal with ⟨hcontext, hdecoded, hok⟩
    exact ⟨hcontext, hdecoded, hok.trans hfinalValue⟩
end Lax47Proofs.RamReductionSemantics
