import Lax47Proofs.RamReductionCorrectness

/-!
Semantic correctness of the resampling and graph-output phases of the fixed
IMP+ reduction.  The preceding file establishes the bounded arithmetic
decoders; this file relates their scalar and array states to the finite
Moser--Tardos execution used in the Lax41 analysis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionSemantics

open Lax47.Machine Lax47.Complexity Lax47.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

lemma canonicalSlot_blowupRank {n : ℕ} (left right : BlowupVertex n) :
    canonicalSlot (n * n) (blowupRank left) (blowupRank right) =
      edgeSlot s(left, right) := by
  rw [edgeSlot_mk]
  by_cases hlt : blowupRank left < blowupRank right
  · rw [canonicalSlot, if_pos hlt, min_eq_left (Nat.le_of_lt hlt),
      max_eq_right (Nat.le_of_lt hlt)]
    rfl
  · have hle : blowupRank right ≤ blowupRank left := by omega
    rw [canonicalSlot, if_neg hlt, min_eq_right hle, max_eq_left hle]
    rfl

lemma decodedFirstRank_eq {n rank : ℕ}
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    decodedFirstRank (n * n) rank =
      blowupRank (executionFirstVertex (tripleAtRank n rank hrank)) := by
  symm
  simpa [decodedFirstRank] using tripleAtRank_first_rank n rank hrank

lemma decodedSecondRank_eq {n rank : ℕ}
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    decodedSecondRank (n * n) rank =
      blowupRank (executionSecondVertex (tripleAtRank n rank hrank)) := by
  symm
  rw [tripleAtRank_second_rank n rank hrank]
  exact (decodedSecondRank_eq_mod _ _).symm

lemma decodedThirdRank_eq {n rank : ℕ}
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    decodedThirdRank (n * n) rank =
      blowupRank (executionThirdVertex (tripleAtRank n rank hrank)) := by
  symm
  rw [tripleAtRank_third_rank n rank hrank]
  exact (decodedThirdRank_eq_mod _ _).symm

lemma decodedFirstBase_eq {n rank : ℕ} (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    decodedFirstRank (n * n) rank / n =
      (executionFirstVertex (tripleAtRank n rank hrank)).1.1 := by
  rw [decodedFirstRank_eq hrank]
  exact blowupRank_div_order hn _

lemma decodedSecondBase_eq {n rank : ℕ} (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    decodedSecondRank (n * n) rank / n =
      (executionSecondVertex (tripleAtRank n rank hrank)).1.1 := by
  rw [decodedSecondRank_eq hrank]
  exact blowupRank_div_order hn _

lemma decodedThirdBase_eq {n rank : ℕ} (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    decodedThirdRank (n * n) rank / n =
      (executionThirdVertex (tripleAtRank n rank hrank)).1.1 := by
  rw [decodedThirdRank_eq hrank]
  exact blowupRank_div_order hn _

lemma decodedEdgeOne_eq {n rank : ℕ}
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    canonicalSlot (n * n) (decodedFirstRank (n * n) rank)
        (decodedSecondRank (n * n) rank) =
      edgeSlot s(executionFirstVertex (tripleAtRank n rank hrank),
        executionSecondVertex (tripleAtRank n rank hrank)) := by
  rw [decodedFirstRank_eq hrank, decodedSecondRank_eq hrank]
  exact canonicalSlot_blowupRank _ _

lemma decodedEdgeTwo_eq {n rank : ℕ}
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    canonicalSlot (n * n) (decodedFirstRank (n * n) rank)
        (decodedThirdRank (n * n) rank) =
      edgeSlot s(executionFirstVertex (tripleAtRank n rank hrank),
        executionThirdVertex (tripleAtRank n rank hrank)) := by
  rw [decodedFirstRank_eq hrank, decodedThirdRank_eq hrank]
  exact canonicalSlot_blowupRank _ _

lemma decodedEdgeThree_eq {n rank : ℕ}
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    canonicalSlot (n * n) (decodedSecondRank (n * n) rank)
        (decodedThirdRank (n * n) rank) =
      edgeSlot s(executionSecondVertex (tripleAtRank n rank hrank),
        executionThirdVertex (tripleAtRank n rank hrank)) := by
  rw [decodedSecondRank_eq hrank, decodedThirdRank_eq hrank]
  exact canonicalSlot_blowupRank _ _

/-- The square counter array agrees with the semantic counter function on
every canonical unordered-edge slot. -/
def CountsRepresent (n : ℕ) (counts : EdgeVariable n → ℕ)
    (state : Env) : Prop :=
  (state.arrs countsArray).length = (n * n) * (n * n) ∧
  ∀ edge, (state.arrs countsArray).getD (edgeSlot edge) 0 = counts edge

lemma CountsRepresent.index_lt {n : ℕ} {counts : EdgeVariable n → ℕ}
    {state : Env} (h : CountsRepresent n counts state) (edge : EdgeVariable n) :
    edgeSlot edge < (state.arrs countsArray).length := by
  rw [h.1]
  exact edgeSlot_lt edge

lemma CountsRepresent.getElem? {n : ℕ} {counts : EdgeVariable n → ℕ}
    {state : Env} (h : CountsRepresent n counts state) (edge : EdgeVariable n) :
    (state.arrs countsArray)[edgeSlot edge]? = some (counts edge) := by
  have hindex := h.index_lt edge
  have hvalue := h.2 edge
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hindex] at hvalue
  simp only [Option.getD_some] at hvalue
  rw [List.getElem?_eq_getElem hindex, hvalue]

def incrementEdgeCount {n : ℕ} (counts : EdgeVariable n → ℕ)
    (target : EdgeVariable n) : EdgeVariable n → ℕ :=
  fun edge => if edge = target then counts edge + 1 else counts edge

lemma CountsRepresent.increment {n : ℕ} {counts : EdgeVariable n → ℕ}
    {state : Env} (h : CountsRepresent n counts state)
    (target : EdgeVariable n) :
    CountsRepresent n (incrementEdgeCount counts target)
      (state.setArr countsArray (edgeSlot target) (counts target + 1)) := by
  constructor
  · simpa using h.1
  · intro edge
    rw [arrs_setArr, if_pos rfl, List.getD_eq_getElem?_getD,
      List.getElem?_set]
    by_cases heq : edge = target
    · subst edge
      rw [if_pos rfl, if_pos (h.index_lt target)]
      simp [incrementEdgeCount]
    · have hslot : edgeSlot target ≠ edgeSlot edge := by
        intro hslots
        exact heq (edgeSlot_injective hslots.symm)
      rw [if_neg hslot, h.getElem? edge]
      simp [incrementEdgeCount, heq]

/-! ### Input adjacency tests -/

def retainIf (value : ℕ) (condition : Bool) : ℕ :=
  if condition then value else 0

@[simp] lemma retainIf_one (condition : Bool) :
    retainIf 1 condition = bitWord condition := by
  cases condition <;> rfl

@[simp] lemma retainIf_bitWord (left right : Bool) :
    retainIf (bitWord left) right = bitWord (left && right) := by
  cases left <;> cases right <;> rfl

theorem requireRawAdjacencyDirection_spec (B n : ℕ) (input : BitString)
    (left right : Fin n) (leftName rightName : String) (initialOk : ℕ)
    (hnB : n < B)
    (hposition : 2 + left.1 * n + right.1 < B) :
    Spec B
      (fun state => HasRawInput input state ∧
        state.vars orderVar = n ∧ state.vars leftName = left.1 ∧
        state.vars rightName = right.1 ∧ state.vars okVar = initialOk ∧
        input.length < B ∧ (∀ value ∈ input, value < B) ∧ 1 < B)
      (requireRawAdjacencyDirection leftName rightName)
      (fun _ state => state.vars okVar =
        retainIf initialOk (rawBit input (2 + left.1 * n + right.1)))
      100 := by
  let position := 2 + left.1 * n + right.1
  have hread := readRawBitVar_spec B input rawIndexVar tempVar position (by decide)
  unfold requireRawAdjacencyDirection Com.block retainIf
  run_vcg [hread]
  all_goals
    simp_all [position, rawIndexVar, orderVar, rawLenVar, tempVar, okVar,
      setZero, bitWord, HasRawInput, Env.setVar]
  all_goals try omega
  all_goals
    cases hbit : rawBit input (2 + left.1 * n + right.1) <;>
      simp_all [retainIf, hbit]
  all_goals omega

theorem requireGraphAdjacency_spec (B n : ℕ) (input : BitString)
    (left right : Fin n) (leftName rightName : String) (initialOk : ℕ)
    (hnB : n < B)
    (hforward : 2 + left.1 * n + right.1 < B)
    (hbackward : 2 + right.1 * n + left.1 < B)
    (hleftSafe : leftName ≠ rawIndexVar ∧ leftName ≠ tempVar ∧
      leftName ≠ okVar)
    (hrightSafe : rightName ≠ rawIndexVar ∧ rightName ≠ tempVar ∧
      rightName ≠ okVar) :
    Spec B
      (fun state => HasRawInput input state ∧
        state.vars orderVar = n ∧ state.vars leftName = left.1 ∧
        state.vars rightName = right.1 ∧ state.vars okVar = initialOk ∧
        input.length < B ∧ (∀ value ∈ input, value < B) ∧ 1 < B)
      (requireGraphAdjacency leftName rightName)
      (fun _ state => state.vars okVar =
        retainIf initialOk ((rawGraphCodeAt n input).adjacent left right))
      250 := by
  have hfirst := requireRawAdjacencyDirection_spec B n input left right
    leftName rightName initialOk hnB hforward
  have hsecond := requireRawAdjacencyDirection_spec B n input
    right left rightName leftName
      (retainIf initialOk (rawBit input (2 + left.1 * n + right.1)))
      hnB hbackward
  have hfirstFrame := hfirst.frame
  have hfirstKeep :
      Spec B
        (fun state => HasRawInput input state ∧
          state.vars orderVar = n ∧ state.vars leftName = left.1 ∧
          state.vars rightName = right.1 ∧ state.vars okVar = initialOk ∧
          input.length < B ∧ (∀ value ∈ input, value < B) ∧ 1 < B)
        (requireRawAdjacencyDirection leftName rightName)
        (fun _ state =>
          state.vars okVar =
              retainIf initialOk (rawBit input (2 + left.1 * n + right.1)) ∧
          HasRawInput input state ∧ state.vars orderVar = n ∧
          state.vars leftName = left.1 ∧ state.vars rightName = right.1)
        100 := by
    apply hfirstFrame.post
    intro initial final hpre hpost
    rcases hpre with
      ⟨hraw, horder, hleft, hright, _hok, _hlen, _hvalues, _hB⟩
    rcases hpost with ⟨hok, hvars, harrs, _hinp, _hout⟩
    refine ⟨hok, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · calc
          final.vars rawLenVar = initial.vars rawLenVar := by
            apply hvars
            simp [requireRawAdjacencyDirection, Com.block, rawLenVar,
              rawIndexVar, tempVar, okVar, readRawBit, setZero, setOne,
              Com.wvars]
          _ = input.length := hraw.1
      · calc
          final.arrs rawArray = initial.arrs rawArray := by
            apply harrs
            simp [requireRawAdjacencyDirection, Com.block, readRawBit,
              setZero, setOne, Com.warrs]
          _ = input := hraw.2
    · calc
        final.vars orderVar = initial.vars orderVar := by
          apply hvars
          simp [requireRawAdjacencyDirection, Com.block, orderVar,
            rawIndexVar, tempVar, okVar, readRawBit, setZero, setOne,
            Com.wvars]
        _ = n := horder
    · calc
        final.vars leftName = initial.vars leftName := by
          apply hvars
          simpa [requireRawAdjacencyDirection, Com.block, rawIndexVar,
            tempVar, okVar, readRawBit, setZero, setOne, Com.wvars] using
            hleftSafe
        _ = left.1 := hleft
    · calc
        final.vars rightName = initial.vars rightName := by
          apply hvars
          simpa [requireRawAdjacencyDirection, Com.block, rawIndexVar,
            tempVar, okVar, readRawBit, setZero, setOne, Com.wvars] using
            hrightSafe
        _ = right.1 := hright
  have hsecondFrame := hsecond.frame
  unfold requireGraphAdjacency rawGraphCodeAt
  by_cases heq : left = right
  · subst right
    run_vcg
    all_goals
      simp_all [setZero, retainIf, okVar, Env.setVar]
  · have hvals : left.1 ≠ right.1 := by
      intro h
      exact heq (Fin.ext h)
    run_vcg [hfirstKeep, hsecondFrame]
    all_goals
      simp_all [heq, hvals, retainIf, okVar, rawLenVar, orderVar,
        rawIndexVar, tempVar,
        requireRawAdjacencyDirection, Com.block, readRawBit, setZero,
        setOne, Com.wvars, Com.warrs, Com.reads, Com.NoWrite]
    all_goals try omega
    all_goals
      cases hforwardBit : rawBit input (2 + left.1 * n + right.1) <;>
      cases hbackwardBit : rawBit input (2 + right.1 * n + left.1) <;>
      simp_all [retainIf, hforwardBit, hbackwardBit]
    all_goals omega

/-! ### Finite Bernoulli blocks -/

/-- Whether every coordinate below `prefix` in one sampled block is true. -/
def sampledPrefix {n : ℕ} (seed : ExecutionSeed n) (edge : EdgeVariable n)
    (row : Fin (executionBudget n + 1)) (prefixLength : ℕ) : Bool :=
  decide (∀ bit : Fin (executionSampleBits n), bit.1 < prefixLength →
    seed edge row bit = true)

@[simp] lemma sampledPrefix_zero {n : ℕ} (seed : ExecutionSeed n)
    (edge : EdgeVariable n) (row : Fin (executionBudget n + 1)) :
    sampledPrefix seed edge row 0 = true := by
  simp [sampledPrefix]

lemma sampledPrefix_succ {n : ℕ} (seed : ExecutionSeed n)
    (edge : EdgeVariable n) (row : Fin (executionBudget n + 1))
    (prefixLength : ℕ) (hprefix : prefixLength < executionSampleBits n) :
    sampledPrefix seed edge row (prefixLength + 1) =
      (sampledPrefix seed edge row prefixLength &&
        seed edge row ⟨prefixLength, hprefix⟩) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sampledPrefix, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro hall
    constructor
    · intro bit hbit
      exact hall bit (by omega)
    · exact hall ⟨prefixLength, hprefix⟩ (by simp)
  · rintro ⟨hprior, hcurrent⟩ bit hbit
    by_cases hlt : bit.1 < prefixLength
    · exact hprior bit hlt
    · have heq : bit = ⟨prefixLength, hprefix⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      simpa [heq] using hcurrent

lemma sampledPrefix_full {n : ℕ} (seed : ExecutionSeed n)
    (edge : EdgeVariable n) (row : Fin (executionBudget n + 1)) :
    sampledPrefix seed edge row (executionSampleBits n) =
      executionBlockValue (seed edge row) := by
  apply Bool.eq_iff_iff.mpr
  simp [sampledPrefix, executionBlockValue]

lemma executionCell_eq_sampledPrefix {n : ℕ} (seed : ExecutionSeed n)
    (edge : EdgeVariable n) (row : ℕ)
    (hrow : row < executionBudget n + 1) :
    executionCell seed edge row =
      sampledPrefix seed edge ⟨row, hrow⟩ (executionSampleBits n) := by
  rw [executionCell, dif_pos hrow, sampledPrefix_full]

/-- State shared by every semantic phase of the reduction. -/
def ExecutionContext (n : ℕ) (input : BitString)
    (counts : EdgeVariable n → ℕ) (state : Env) : Prop :=
  HasRawInput input state ∧ HasParameters n state ∧
  state.vars sampleBitsVar = executionSampleBits n ∧
  CountsRepresent n counts state

/-- Arithmetic position of one fair bit in the paired machine word. -/
def sampleInputPosition (n slot row bit : ℕ) : ℕ :=
  2 + n * n + ((slot * (executionBudget n + 1) + row) *
    executionSampleBits n + bit)

lemma sampleInputPosition_eq_flatBitIndex {n : ℕ} (edge : EdgeVariable n)
    (row : Fin (executionBudget n + 1))
    (bit : Fin (executionSampleBits n)) :
    sampleInputPosition n (edgeSlot edge) row.1 bit.1 =
      2 + n * n + (flatBitIndex edge row bit).1 := by
  rfl

lemma sampleInputPosition_lt {n B : ℕ} (edge : EdgeVariable n)
    (row : Fin (executionBudget n + 1))
    (bit : Fin (executionSampleBits n))
    (hB : 2 + n * n + flatRandomBitCount n < B) :
    sampleInputPosition n (edgeSlot edge) row.1 bit.1 < B := by
  rw [sampleInputPosition_eq_flatBitIndex]
  have := (flatBitIndex edge row bit).2
  omega

/-- One loop iteration reads precisely the next bit of the selected structured
sample and updates the running conjunction. -/
theorem sampleBitBody_spec (B : ℕ) {n : ℕ} (input : BitString)
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ)
    (edge : EdgeVariable n) (edgeName : String)
    (row : ℕ) (hrow : row < executionBudget n + 1) (initialOk : ℕ)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hedgeSafe : edgeName ≠ rawIndexVar ∧ edgeName ≠ tempVar ∧
      edgeName ≠ okVar ∧ edgeName ≠ bitVar) :
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        state.vars edgeName = edgeSlot edge ∧ state.vars rowVar = row ∧
        state.vars bitVar < executionSampleBits n ∧
        state.vars okVar = retainIf initialOk
          (sampledPrefix (executionSeedOfFlat flatSeed) edge ⟨row, hrow⟩
            (state.vars bitVar)))
      (sampleBitBody edgeName)
      (fun initial final =>
        ExecutionContext n input counts final ∧
        final.vars edgeName = edgeSlot edge ∧ final.vars rowVar = row ∧
        final.vars bitVar = initial.vars bitVar + 1 ∧
        final.vars okVar = retainIf initialOk
          (sampledPrefix (executionSeedOfFlat flatSeed) edge ⟨row, hrow⟩
            (final.vars bitVar)))
      200 := by
  unfold Spec
  intro initial hstate
  rcases hstate with ⟨hcontext, hedge, hrowState, hbit, hok⟩
  rcases hcontext with ⟨hraw, hparameters, hsampleBits, hcounts⟩
  rcases hparameters with
    ⟨horder, hblowup, hcountLen, htripleLen, hbudget, htarget⟩
  let bit : Fin (executionSampleBits n) := ⟨initial.vars bitVar, hbit⟩
  let rowFin : Fin (executionBudget n + 1) := ⟨row, hrow⟩
  let position := sampleInputPosition n (edgeSlot edge) row bit
  have hpositionB : position < B := by
    exact sampleInputPosition_lt edge rowFin bit hB
  change 2 + n * n +
      ((edgeSlot edge * (executionBudget n + 1) + row) *
        executionSampleBits n + initial.vars bitVar) < B at hpositionB
  have hflatB :
      (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n < B := by
    unfold flatRandomBitCount blowupOrder at hB
    omega
  have hslotLt := edgeSlot_lt edge
  simp only [blowupOrder] at hslotLt
  have hsamplePos : 0 < executionSampleBits n := by
    simp [executionSampleBits]
  have htotalPos : 0 < (n * n) * (n * n) := by omega
  have htotalOne : 1 ≤ (n * n) * (n * n) := htotalPos
  have hbudgetOne : 1 ≤ executionBudget n + 1 := by omega
  have hsampleOne : 1 ≤ executionSampleBits n := hsamplePos
  have htotalLeFlat :
      (n * n) * (n * n) ≤
        (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by
    calc
      (n * n) * (n * n) =
          (n * n) * (n * n) * 1 * 1 := by simp
      _ ≤ (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by gcongr
  have hbudgetLeFlat :
      executionBudget n + 1 ≤
        (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by
    calc
      executionBudget n + 1 =
          1 * (executionBudget n + 1) * 1 := by simp
      _ ≤ (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by gcongr
  have hsampleLeFlat :
      executionSampleBits n ≤
        (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by
    calc
      executionSampleBits n = 1 * 1 * executionSampleBits n := by simp
      _ ≤ (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by gcongr
  have hslotTimesBudgetLeFlat :
      edgeSlot edge * (executionBudget n + 1) ≤
        (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by
    calc
      edgeSlot edge * (executionBudget n + 1) =
          edgeSlot edge * (executionBudget n + 1) * 1 := by simp
      _ ≤ (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by gcongr
  have hslotRowLt :
      edgeSlot edge * (executionBudget n + 1) + row <
        (n * n) * (n * n) * (executionBudget n + 1) := by
    calc
      edgeSlot edge * (executionBudget n + 1) + row <
          edgeSlot edge * (executionBudget n + 1) +
            (executionBudget n + 1) := by omega
      _ = (edgeSlot edge + 1) * (executionBudget n + 1) := by ring
      _ ≤ (n * n) * (n * n) * (executionBudget n + 1) := by
        gcongr
        omega
  have hslotRowTimesSampleLt :
      (edgeSlot edge * (executionBudget n + 1) + row) *
          executionSampleBits n <
        (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by
    exact Nat.mul_lt_mul_of_pos_right hslotRowLt hsamplePos
  have hseedOffsetLt :
      (edgeSlot edge * (executionBudget n + 1) + row) *
            executionSampleBits n + initial.vars bitVar <
        (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by
    calc
      (edgeSlot edge * (executionBudget n + 1) + row) *
            executionSampleBits n + initial.vars bitVar <
          (edgeSlot edge * (executionBudget n + 1) + row) *
              executionSampleBits n + executionSampleBits n := by omega
      _ = (edgeSlot edge * (executionBudget n + 1) + row + 1) *
          executionSampleBits n := by ring
      _ ≤ (n * n) * (n * n) * (executionBudget n + 1) *
          executionSampleBits n := by
        gcongr
        omega
  have hnOne : 1 ≤ n := by
    cases n with
    | zero => simp at htotalPos
    | succ n => omega
  have hnLeSquare : n ≤ n * n := by
    calc
      n = n * 1 := by simp
      _ ≤ n * n := by gcongr
  have hsquareOne : 1 ≤ n * n := by
    calc
      1 = 1 * 1 := by simp
      _ ≤ n * n := by gcongr
  have hsquareLeTotal : n * n ≤ (n * n) * (n * n) := by
    calc
      n * n = (n * n) * 1 := by simp
      _ ≤ (n * n) * (n * n) := by gcongr
  have htotalB : (n * n) * (n * n) < B :=
    lt_of_le_of_lt htotalLeFlat hflatB
  have hnB : n < B :=
    lt_of_le_of_lt (hnLeSquare.trans hsquareLeTotal) htotalB
  have hnSquareB : n * n < B :=
    lt_of_le_of_lt hsquareLeTotal htotalB
  have hslotB : edgeSlot edge < B := hslotLt.trans htotalB
  have hbudgetSuccB : executionBudget n + 1 < B :=
    lt_of_le_of_lt hbudgetLeFlat hflatB
  have hbudgetB : executionBudget n < B := by omega
  have hsampleB : executionSampleBits n < B :=
    lt_of_le_of_lt hsampleLeFlat hflatB
  have hslotTimesBudgetB : edgeSlot edge * (executionBudget n + 1) < B :=
    lt_of_le_of_lt hslotTimesBudgetLeFlat hflatB
  have hslotRowB :
      edgeSlot edge * (executionBudget n + 1) + row < B := by
    have hle :
        edgeSlot edge * (executionBudget n + 1) + row ≤
          (edgeSlot edge * (executionBudget n + 1) + row) *
            executionSampleBits n := by
      calc
        edgeSlot edge * (executionBudget n + 1) + row =
            (edgeSlot edge * (executionBudget n + 1) + row) * 1 := by simp
        _ ≤ (edgeSlot edge * (executionBudget n + 1) + row) *
            executionSampleBits n := by gcongr
    exact lt_of_le_of_lt hle (hslotRowTimesSampleLt.trans hflatB)
  have hslotRowTimesSampleB :
      (edgeSlot edge * (executionBudget n + 1) + row) *
          executionSampleBits n < B := hslotRowTimesSampleLt.trans hflatB
  have hseedOffsetB :
      (edgeSlot edge * (executionBudget n + 1) + row) *
      executionSampleBits n + initial.vars bitVar < B :=
    hseedOffsetLt.trans hflatB
  have hOneB : 1 < B := by omega
  let indexExpr : Expr :=
    .add (.add (.lit 2) (.mul (.var orderVar) (.var orderVar)))
      (.add
        (.mul
          (.add
            (.mul (.var edgeName) (.add (.var budgetVar) (.lit 1)))
            (.var rowVar))
          (.var sampleBitsVar))
        (.var bitVar))
  have hindexEval : indexExpr.evalB B initial = some position := by
    simp [indexExpr, position, sampleInputPosition, horder, hedge, hbudget,
      hrowState, hsampleBits, hnB, hnSquareB, hslotB, hbudgetB,
      hbudgetSuccB, hslotTimesBudgetB, hslotRowB, hsampleB,
      hslotRowTimesSampleB, hseedOffsetB, hpositionB, bit] <;> omega
  have hassign :
      Spec B (fun state => state = initial)
        (.assign rawIndexVar indexExpr)
        (fun _ final => final = initial.setVar rawIndexVar position) 18 := by
    have hbase := Spec.assign (P := fun state => state = initial)
      (x := rawIndexVar) (e := indexExpr) (f := fun _ => position) (by
        intro state hstate
        subst state
        exact hindexEval)
    apply hbase.post
    intro start final hstart hpost
    subst start
    exact hpost
  have hread := readRawBitVar_spec B input
    rawIndexVar tempVar position (by decide)
  have hreadReady := hread.pre
    (P' := fun state => state = initial.setVar rawIndexVar position) (by
      intro state hstate
      subst state
      refine ⟨?_, ?_, hpositionB, hinputB, hvaluesB, hOneB⟩
      · simpa [HasRawInput, Env.setVar, rawIndexVar, rawLenVar] using hraw
      · simp [Env.setVar, rawIndexVar])
  have hrawBit : rawBit input position =
      flatSeed (flatBitIndex edge rowFin bit) := by
    rw [show position = 2 + n * n + (flatBitIndex edge rowFin bit).1 by rfl]
    exact model.seed_bit (flatBitIndex edge rowFin bit)
  have hprefixSucc :
      sampledPrefix (executionSeedOfFlat flatSeed) edge rowFin
          (initial.vars bitVar + 1) =
        (sampledPrefix (executionSeedOfFlat flatSeed) edge rowFin
            (initial.vars bitVar) &&
          flatSeed (flatBitIndex edge rowFin bit)) := by
    exact sampledPrefix_succ _ _ _ _ hbit
  clear hflatB hslotLt hsamplePos htotalPos htotalOne hbudgetOne
    hsampleOne htotalLeFlat hbudgetLeFlat hsampleLeFlat
    hslotTimesBudgetLeFlat hslotRowLt hslotRowTimesSampleLt hseedOffsetLt
    hnOne hnLeSquare hsquareOne hsquareLeTotal htotalB hnB hnSquareB
    hslotB hbudgetSuccB hbudgetB hsampleB hslotTimesBudgetB hslotRowB
    hslotRowTimesSampleB hseedOffsetB hindexEval hread
  cases hp : sampledPrefix (executionSeedOfFlat flatSeed) edge rowFin
    (initial.vars bitVar) <;>
  cases hb : flatSeed (flatBitIndex edge rowFin bit)
  all_goals unfold sampleBitBody Com.block increment
  all_goals run_vcg [hassign, hreadReady]
  all_goals
    simp_all [ExecutionContext, HasRawInput, HasParameters, CountsRepresent,
      sampleInputPosition, position, bit, rowFin, retainIf, hrawBit,
      hprefixSucc, Env.setVar, rawIndexVar, tempVar, okVar,
      bitVar, rowVar, orderVar, budgetVar, sampleBitsVar, rawLenVar,
      blowupVar, countLenVar, tripleLenVar, sampleTargetVar, countsArray,
      bitWord]
  all_goals try omega

def SampleLoopInvariant {n : ℕ} (input : BitString) (graph : GraphCode n)
    (flatSeed : FlatExecutionSeed n)
    (_model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ)
    (edge : EdgeVariable n) (edgeName : String) (row : ℕ)
    (hrow : row < executionBudget n + 1) (initialOk : ℕ)
    (state : Env) : Prop :=
  ExecutionContext n input counts state ∧
  state.vars edgeName = edgeSlot edge ∧ state.vars rowVar = row ∧
  state.vars bitVar ≤ executionSampleBits n ∧
  state.vars okVar = retainIf initialOk
    (sampledPrefix (executionSeedOfFlat flatSeed) edge ⟨row, hrow⟩
      (state.vars bitVar))

theorem sampleBlockLoop_spec (B : ℕ) {n : ℕ} (input : BitString)
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ)
    (edge : EdgeVariable n) (edgeName : String)
    (row : ℕ) (hrow : row < executionBudget n + 1) (initialOk : ℕ)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : input.length < B)
    (hvaluesB : ∀ value ∈ input, value < B)
    (hsampleB : executionSampleBits n < B)
    (hedgeSafe : edgeName ≠ rawIndexVar ∧ edgeName ≠ tempVar ∧
      edgeName ≠ okVar ∧ edgeName ≠ bitVar) :
    Spec B
      (fun state =>
        ExecutionContext n input counts state ∧
        state.vars edgeName = edgeSlot edge ∧ state.vars rowVar = row ∧
        state.vars okVar = initialOk)
      (sampleBlockLoop edgeName)
      (fun _ final =>
        ExecutionContext n input counts final ∧
        final.vars edgeName = edgeSlot edge ∧ final.vars rowVar = row ∧
        final.vars bitVar = executionSampleBits n ∧
        final.vars okVar = retainIf initialOk
          (sampledPrefix (executionSeedOfFlat flatSeed) edge ⟨row, hrow⟩
            (executionSampleBits n)))
      ((200 + 4) * executionSampleBits n + 6) := by
  let invariant := SampleLoopInvariant input graph flatSeed model counts edge edgeName row hrow initialOk
  have hbodyBase := sampleBitBody_spec B input graph flatSeed model counts edge edgeName row hrow
    initialOk hB hinputB hvaluesB hedgeSafe
  have hbody :
      Spec B (fun state => invariant state ∧
          state.vars bitVar < executionSampleBits n)
        (sampleBitBody edgeName)
        (fun initial final => invariant final ∧
          final.vars bitVar = initial.vars bitVar + 1) 200 := by
    apply hbodyBase.conseq
    · intro state hstate
      rcases hstate with
        ⟨⟨hcontext, hedge, hrowState, _hbitLe, hok⟩, hbit⟩
      exact ⟨hcontext, hedge, hrowState, hbit, hok⟩
    · intro initial final hpre hpost
      rcases hpre with ⟨hinvariant, hbit⟩
      rcases hpost with ⟨hcontext, hedge, hrowState, hnext, hok⟩
      refine ⟨⟨hcontext, hedge, hrowState, ?_, hok⟩, hnext⟩
      omega
    · rfl
  have hloop := Spec.forRangeZero bitVar sampleBitsVar invariant
    (executionSampleBits n) 200 hsampleB
    (fun _ hstate => hstate.2.2.2.1)
    (fun _ hstate => hstate.1.2.2.1)
    hbody
  unfold sampleBlockLoop
  apply hloop.conseq
  · intro state hstate
    rcases hstate with ⟨hcontext, hedge, hrowState, hok⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [ExecutionContext, HasRawInput, HasParameters, CountsRepresent,
        Env.setVar, bitVar, rawLenVar, orderVar, blowupVar, countLenVar,
        tripleLenVar, budgetVar, sampleTargetVar, sampleBitsVar,
        countsArray] using hcontext
    · have hedgeBit : edgeName ≠ bitVar := hedgeSafe.2.2.2
      simpa only [vars_setVar, if_neg hedgeBit] using hedge
    · simpa [Env.setVar, bitVar, rowVar] using hrowState
    · simp [Env.setVar, bitVar]
    · have hokBit : okVar ≠ bitVar := by decide
      simpa [vars_setVar, hokBit, sampledPrefix_zero, retainIf] using hok
  · intro _ final _ hpost
    rcases hpost with
      ⟨⟨hcontext, hedge, hrowState, _hbitLe, hok⟩, hbit⟩
    exact ⟨hcontext, hedge, hrowState, hbit, by simpa [hbit] using hok⟩
  · rfl

theorem requireSampledEdge_spec (B : ℕ) {n : ℕ} (input : BitString)
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (model : ModelsReductionInput input graph flatSeed)
    (counts : EdgeVariable n → ℕ)
    (edge : EdgeVariable n) (edgeName : String) (initialOk : ℕ)
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
        state.vars edgeName = edgeSlot edge ∧ state.vars okVar = initialOk)
      (requireSampledEdge edgeName)
      (fun _ final =>
        ExecutionContext n input counts final ∧
        final.vars edgeName = edgeSlot edge ∧
        final.vars okVar = retainIf initialOk
          (executionCell (executionSeedOfFlat flatSeed) edge (counts edge)))
      ((200 + 4) * executionSampleBits n + 100) := by
  have hslotLt : edgeSlot edge < (n * n) * (n * n) := by
    simpa [blowupOrder] using edgeSlot_lt edge
  have hslotB : edgeSlot edge < B := hslotLt.trans hcountLenB
  unfold Spec
  intro initial hpre
  rcases hpre with ⟨hcontext, hedge, hok⟩
  have hcountIndex :
      edgeSlot edge < (initial.arrs countsArray).length :=
    hcontext.2.2.2.index_lt edge
  have hcountValue :
      (initial.arrs countsArray).getD (edgeSlot edge) 0 = counts edge :=
    hcontext.2.2.2.2 edge
  have hcountValueOptional :
      (initial.arrs countsArray)[edgeSlot edge]?.getD 0 = counts edge := by
    rw [← List.getD_eq_getElem?_getD, hcountValue]
  have hcountGet :
      (initial.arrs countsArray)[edgeSlot edge]'hcountIndex = counts edge := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hcountIndex] at hcountValue
    simpa using hcountValue
  have hcountWord :
      (initial.arrs countsArray).getD (edgeSlot edge) 0 < B := by
    rw [hcountValue]
    exact hcountsB edge
  have hcountWordOptional :
      (initial.arrs countsArray)[edgeSlot edge]?.getD 0 < B := by
    rw [hcountValueOptional]
    exact hcountsB edge
  by_cases hrow : counts edge < executionBudget n + 1
  · have hloop := sampleBlockLoop_spec B input graph flatSeed model counts edge edgeName
      (counts edge) hrow initialOk hB hinputB hvaluesB hsampleB
      ⟨hedgeSafe.2.1, hedgeSafe.2.2.1, hedgeSafe.2.2.2.1,
        hedgeSafe.2.2.2.2⟩
    have hcell := executionCell_eq_sampledPrefix
      (executionSeedOfFlat flatSeed) edge (counts edge) hrow
    unfold requireSampledEdge Com.block
    run_vcg [hloop]
    all_goals
      simp_all [ExecutionContext, HasRawInput, HasParameters, CountsRepresent,
        retainIf, hcell, Env.setVar, edgeSlot_lt,
        rowVar, rawIndexVar, tempVar, okVar, bitVar, orderVar, blowupVar,
        countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
        sampleBitsVar, rawLenVar, countsArray]
    all_goals omega
  · have hcell : executionCell (executionSeedOfFlat flatSeed) edge
        (counts edge) = false := by
      rw [executionCell, dif_neg hrow]
    have hdead :
        Spec B (fun _ => False) (sampleBlockLoop edgeName)
          (fun _ _ => False)
          ((200 + 4) * executionSampleBits n + 6) := by
      intro state hfalse
      exact hfalse.elim
    unfold requireSampledEdge Com.block
    run_vcg [hdead]
    all_goals
      simp_all [ExecutionContext, HasRawInput, HasParameters, CountsRepresent,
        retainIf, hcell, Env.setVar, edgeSlot_lt,
        rowVar, rawIndexVar, tempVar, okVar, bitVar, orderVar, blowupVar,
        countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
        sampleBitsVar, rawLenVar, countsArray]
    all_goals omega

/- Temporary theorem-sized checking boundary.

/-! ### Context-preserving elementary tests -/

theorem requireGraphAdjacency_context_spec (B : ℕ) {n : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (counts : EdgeVariable n → ℕ) (left right : Fin n)
    (leftName rightName : String) (initialOk : ℕ)
    (hnB : n < B)
    (hforward : 2 + left.1 * n + right.1 < B)
    (hbackward : 2 + right.1 * n + left.1 < B)
    (hinputB : (pairBits graph.bits flatSeed.bits).length < B)
    (hvaluesB : ∀ value ∈ pairBits graph.bits flatSeed.bits, value < B)
    (hleftSafe : leftName ≠ rawIndexVar ∧ leftName ≠ tempVar ∧
      leftName ≠ okVar)
    (hrightSafe : rightName ≠ rawIndexVar ∧ rightName ≠ tempVar ∧
      rightName ≠ okVar) :
    Spec B
      (fun state =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts state ∧
        state.vars leftName = left.1 ∧ state.vars rightName = right.1 ∧
        state.vars okVar = initialOk)
      (requireGraphAdjacency leftName rightName)
      (fun _ final =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts final ∧
        final.vars leftName = left.1 ∧ final.vars rightName = right.1 ∧
        final.vars okVar = retainIf initialOk (graph.adjacent left right))
      250 := by
  have hbase := requireGraphAdjacency_spec B n
    (pairBits graph.bits flatSeed.bits) left right leftName rightName initialOk
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
    have hdecoded := rawGraphCodeAt_pairBits graph flatSeed
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
            _ = (pairBits graph.bits flatSeed.bits).length := hraw.1
        · calc
            final.arrs rawArray = initial.arrs rawArray := by
              apply harrs
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.warrs]
            _ = pairBits graph.bits flatSeed.bits := hraw.2
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals
          first
          | exact (hvars _ (by
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.wvars])) |>.trans horder
          | exact (hvars _ (by
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.wvars])) |>.trans hblowup
          | exact (hvars _ (by
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.wvars])) |>.trans hcountLen
          | exact (hvars _ (by
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.wvars])) |>.trans htripleLen
          | exact (hvars _ (by
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.wvars])) |>.trans hbudget
          | exact (hvars _ (by
              simp [requireGraphAdjacency, requireRawAdjacencyDirection,
                Com.block, readRawBit, setZero, setOne, Com.wvars])) |>.trans htarget
      · exact (hvars _ (by
          simp [requireGraphAdjacency, requireRawAdjacencyDirection,
            Com.block, readRawBit, setZero, setOne, Com.wvars])) |>.trans hsample
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
    · exact (hvars leftName (by
        simpa [requireGraphAdjacency, requireRawAdjacencyDirection,
          Com.block, readRawBit, setZero, setOne, Com.wvars] using
          ⟨hleftSafe, hrightSafe⟩)).trans hleft
    · exact (hvars rightName (by
        simpa [requireGraphAdjacency, requireRawAdjacencyDirection,
          Com.block, readRawBit, setZero, setOne, Com.wvars] using
          ⟨hleftSafe, hrightSafe⟩)).trans hright
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
      · exact (hvars rawLenVar (by
          simp [decodeTriple, decodeTripleRanks, decodeTripleEdges,
            edgeSlotCom, Com.block, Com.wvars, rawLenVar])).trans hraw.1
      · rw [harrs rawArray]
        · exact hraw.2
        · simp [decodeTriple, decodeTripleRanks, decodeTripleEdges,
            edgeSlotCom, Com.block, Com.warrs]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals
        first
        | exact (hvars _ (by simp [decodeTriple, decodeTripleRanks,
            decodeTripleEdges, edgeSlotCom, Com.block, Com.wvars])).trans horder
        | exact (hvars _ (by simp [decodeTriple, decodeTripleRanks,
            decodeTripleEdges, edgeSlotCom, Com.block, Com.wvars])).trans hblowup
        | exact (hvars _ (by simp [decodeTriple, decodeTripleRanks,
            decodeTripleEdges, edgeSlotCom, Com.block, Com.wvars])).trans hcountLen
        | exact (hvars _ (by simp [decodeTriple, decodeTripleRanks,
            decodeTripleEdges, edgeSlotCom, Com.block, Com.wvars])).trans htripleLen
        | exact (hvars _ (by simp [decodeTriple, decodeTripleRanks,
            decodeTripleEdges, edgeSlotCom, Com.block, Com.wvars])).trans hbudget
        | exact (hvars _ (by simp [decodeTriple, decodeTripleRanks,
            decodeTripleEdges, edgeSlotCom, Com.block, Com.wvars])).trans htarget
    · exact (hvars sampleBitsVar (by simp [decodeTriple, decodeTripleRanks,
        decodeTripleEdges, edgeSlotCom, Com.block, Com.wvars,
        sampleBitsVar])).trans hsample
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
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (counts : EdgeVariable n → ℕ) (left right : Fin n)
    (leftName rightName : String) (initialOk : ℕ)
    (hnB : n < B)
    (hforward : 2 + left.1 * n + right.1 < B)
    (hbackward : 2 + right.1 * n + left.1 < B)
    (hinputB : (pairBits graph.bits flatSeed.bits).length < B)
    (hvaluesB : ∀ value ∈ pairBits graph.bits flatSeed.bits, value < B)
    (hleftSafe : leftName ≠ rawIndexVar ∧ leftName ≠ tempVar ∧
      leftName ≠ okVar)
    (hrightSafe : rightName ≠ rawIndexVar ∧ rightName ≠ tempVar ∧
      rightName ≠ okVar) :
    Spec B
      (fun state =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts state ∧
        HasDecodedTriple n rank state ∧
        state.vars leftName = left.1 ∧ state.vars rightName = right.1 ∧
        state.vars okVar = initialOk)
      (requireGraphAdjacency leftName rightName)
      (fun _ final =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts final ∧
        HasDecodedTriple n rank final ∧
        final.vars okVar = retainIf initialOk (graph.adjacent left right))
      250 := by
  have hbase := requireGraphAdjacency_context_spec B graph flatSeed counts
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
    refine ⟨hcontext, ?_, hok⟩
    simpa only [HasDecodedTriple, HasDecodedRanks,
      hvars blowupVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars firstVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars secondVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars thirdVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars firstBaseVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars secondBaseVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars thirdBaseVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars edgeOneVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars edgeTwoVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars]),
      hvars edgeThreeVar (by
        simp [requireGraphAdjacency, requireRawAdjacencyDirection, Com.block,
          readRawBit, setZero, setOne, Com.wvars])] using hdecoded
  · rfl

theorem requireSampledEdge_decoded_spec (B : ℕ) {n rank : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (counts : EdgeVariable n → ℕ) (edge : EdgeVariable n)
    (edgeName : String) (initialOk : ℕ)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (hinputB : (pairBits graph.bits flatSeed.bits).length < B)
    (hvaluesB : ∀ value ∈ pairBits graph.bits flatSeed.bits, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B)
    (hedgeSafe : edgeName ≠ rowVar ∧ edgeName ≠ rawIndexVar ∧
      edgeName ≠ tempVar ∧ edgeName ≠ okVar ∧ edgeName ≠ bitVar) :
    Spec B
      (fun state =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts state ∧
        HasDecodedTriple n rank state ∧ state.vars edgeName = edgeSlot edge ∧
        state.vars okVar = initialOk)
      (requireSampledEdge edgeName)
      (fun _ final =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts final ∧
        HasDecodedTriple n rank final ∧
        final.vars okVar = retainIf initialOk
          (executionCell (executionSeedOfFlat flatSeed) edge (counts edge)))
      ((200 + 4) * executionSampleBits n + 100) := by
  have hbase := requireSampledEdge_spec B graph flatSeed counts edge edgeName
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
    refine ⟨hcontext, ?_, hok⟩
    simpa only [HasDecodedTriple, HasDecodedRanks,
      hvars blowupVar (by decide),
      hvars firstVar (by decide),
      hvars secondVar (by decide),
      hvars thirdVar (by decide),
      hvars firstBaseVar (by decide),
      hvars secondBaseVar (by decide),
      hvars thirdBaseVar (by decide),
      hvars edgeOneVar (by decide),
      hvars edgeTwoVar (by decide),
      hvars edgeThreeVar (by decide)] using hdecoded
  · rfl

/-! ### The complete triangle predicate -/

theorem testCurrentTriple_spec (B : ℕ) {n rank : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (counts : EdgeVariable n → ℕ)
    (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n))
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : (pairBits graph.bits flatSeed.bits).length < B)
    (hvaluesB : ∀ value ∈ pairBits graph.bits flatSeed.bits, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let triple := tripleAtRank n rank hrank
    Spec B
      (fun state =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts state ∧
        state.vars rankVar = rank)
      testCurrentTriple
      (fun _ final =>
        ExecutionContext n (pairBits graph.bits flatSeed.bits) counts final ∧
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
    (pairBits graph.bits flatSeed.bits) counts hn hrank htripleB
  have hadjOne := requireGraphAdjacency_decoded_spec (rank := rank) B graph flatSeed counts
    first.1 second.1 firstBaseVar secondBaseVar 1 hnB
    (adjacencyPositionB first.1 second.1)
    (adjacencyPositionB second.1 first.1) hinputB hvaluesB
    (by decide) (by decide)
  have hadjTwo := requireGraphAdjacency_decoded_spec (rank := rank) B graph flatSeed counts
    first.1 third.1 firstBaseVar thirdBaseVar afterFirstAdj hnB
    (adjacencyPositionB first.1 third.1)
    (adjacencyPositionB third.1 first.1) hinputB hvaluesB
    (by decide) (by decide)
  have hadjThree := requireGraphAdjacency_decoded_spec (rank := rank) B graph flatSeed counts
    second.1 third.1 secondBaseVar thirdBaseVar afterSecondAdj hnB
    (adjacencyPositionB second.1 third.1)
    (adjacencyPositionB third.1 second.1) hinputB hvaluesB
    (by decide) (by decide)
  have hedgeOne := requireSampledEdge_decoded_spec (rank := rank) B graph flatSeed counts
    edgeOne edgeOneVar afterThirdAdj hB hinputB hvaluesB hbudgetB
    hsampleB hcountLenB hcountsB (by decide)
  have hedgeTwo := requireSampledEdge_decoded_spec (rank := rank) B graph flatSeed counts
    edgeTwo edgeTwoVar afterEdgeOne hB hinputB hvaluesB hbudgetB
    hsampleB hcountLenB hcountsB (by decide)
  have hedgeThree := requireSampledEdge_decoded_spec (rank := rank) B graph flatSeed counts
    edgeThree edgeThreeVar afterEdgeTwo hB hinputB hvaluesB hbudgetB
    hsampleB hcountLenB hcountsB (by decide)
  unfold testCurrentTriple Com.block
  run_vcg [hdecode, hadjOne, hadjTwo, hadjThree,
    hedgeOne, hedgeTwo, hedgeThree]
  all_goals
    simp_all [ExecutionContext, HasParameters, HasDecodedTriple,
      HasDecodedRanks, decodedFirstBase_eq hn hrank,
      decodedSecondBase_eq hn hrank, decodedThirdBase_eq hn hrank,
      decodedEdgeOne_eq hrank, decodedEdgeTwo_eq hrank,
      decodedEdgeThree_eq hrank, triple, first, second, third, edgeOne,
      edgeTwo, edgeThree, firstAdj, secondAdj, thirdAdj, afterFirstAdj,
      afterSecondAdj, afterThirdAdj, afterEdgeOne, afterEdgeTwo,
      executionViolates, executionBlowupAdjacent, retainIf, setOne,
      Env.setVar, okVar]
  all_goals try omega
  all_goals aesop

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

theorem scanTriplesBody_spec (B : ℕ) {n : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (counts : EdgeVariable n → ℕ)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : (pairBits graph.bits flatSeed.bits).length < B)
    (hvaluesB : ∀ value ∈ pairBits graph.bits flatSeed.bits, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let seed := executionSeedOfFlat flatSeed
    let input := pairBits graph.bits flatSeed.bits
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
  let input := pairBits graph.bits flatSeed.bits
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  unfold Spec
  intro initial hstate
  rcases hstate with ⟨hinvariant, hrank⟩
  let rank := initial.vars rankVar
  have htest := testCurrentTriple_spec B graph flatSeed counts hn hrank hB
    htripleB hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
  cases hselection : executionSelectionPrefix graph seed counts rank with
  | none =>
      cases hviolates : executionViolates graph seed counts
        (tripleAtRank n rank hrank)
      · unfold scanTriplesBody rememberCurrentTriple Com.block increment
        run_vcg [htest]
        all_goals
          simp_all [ScanInvariant, SelectionRepresent,
            executionSelectionPrefix_succ graph seed counts hrank,
            hselection, hviolates, rank, seed, input, testCost, setZero,
            setOne, Env.setVar, foundVar, selectedVar,
            selectedEdgeOneVar, selectedEdgeTwoVar, selectedEdgeThreeVar,
            edgeOneVar, edgeTwoVar, edgeThreeVar, rankVar, okVar,
            ExecutionContext, HasParameters, HasDecodedTriple,
            HasDecodedRanks, bitWord]
        all_goals try omega
        all_goals aesop
      · unfold scanTriplesBody rememberCurrentTriple Com.block increment
        run_vcg [htest]
        all_goals
          simp_all [ScanInvariant, SelectionRepresent,
            executionSelectionPrefix_succ graph seed counts hrank,
            hselection, hviolates, rank, seed, input, testCost, setZero,
            setOne, Env.setVar, foundVar, selectedVar,
            selectedEdgeOneVar, selectedEdgeTwoVar, selectedEdgeThreeVar,
            edgeOneVar, edgeTwoVar, edgeThreeVar, rankVar, okVar,
            ExecutionContext, HasParameters, HasDecodedTriple,
            HasDecodedRanks, bitWord, decodedEdgeOne_eq hrank,
            decodedEdgeTwo_eq hrank, decodedEdgeThree_eq hrank]
        all_goals try omega
        all_goals aesop
  | some selected =>
      unfold scanTriplesBody rememberCurrentTriple Com.block increment
      run_vcg
      all_goals
        simp_all [ScanInvariant, SelectionRepresent,
          executionSelectionPrefix_succ graph seed counts hrank,
          hselection, rank, seed, input, testCost, setZero, setOne,
          Env.setVar, foundVar, selectedVar, selectedEdgeOneVar,
          selectedEdgeTwoVar, selectedEdgeThreeVar, edgeOneVar, edgeTwoVar,
          edgeThreeVar, rankVar, okVar, ExecutionContext, HasParameters]
      all_goals try omega
      all_goals aesop

lemma executionSelectionPrefix_full {n : ℕ} (graph : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ) :
    executionSelectionPrefix graph seed counts
        ((n * n) * (n * n) * (n * n)) =
      (findExecutionViolation graph seed counts).1 := by
  rw [show (n * n) * (n * n) * (n * n) =
      (executionTriples n).length by simp]
  simp [executionSelectionPrefix, findExecutionViolation]

theorem scanTriples_spec (B : ℕ) {n : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (counts : EdgeVariable n → ℕ)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : (pairBits graph.bits flatSeed.bits).length < B)
    (hvaluesB : ∀ value ∈ pairBits graph.bits flatSeed.bits, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsB : ∀ edge, counts edge < B) :
    let seed := executionSeedOfFlat flatSeed
    let input := pairBits graph.bits flatSeed.bits
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
  let input := pairBits graph.bits flatSeed.bits
  let tripleCount := (n * n) * (n * n) * (n * n)
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  let bodyCost := testCost + 200
  let scanCost := (bodyCost + 4) * tripleCount + 100
  let invariant := ScanInvariant graph seed counts input
  have hbodyBase := scanTriplesBody_spec B graph flatSeed counts hn hB
    htripleB hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
  have hbody :
      Spec B (fun state => invariant state ∧ state.vars rankVar < tripleCount)
        scanTriplesBody
        (fun initial final => invariant final ∧
          final.vars rankVar = initial.vars rankVar + 1)
        bodyCost := by
    simpa only [seed, input, tripleCount, testCost, bodyCost] using hbodyBase
  have hloop := Spec.forRangeZero rankVar tripleLenVar invariant
    tripleCount bodyCost (by dsimp [tripleCount]; omega)
    (fun _ hstate => hstate.2.1)
    (fun _ hstate => by
      simpa only [invariant, ScanInvariant, tripleCount] using
        hstate.1.2.1.2.2.2.1)
    hbody
  unfold scanTriples Com.block scanTriplesLoop
  run_vcg [hloop]
  all_goals
    simp_all [invariant, ScanInvariant, SelectionRepresent,
      executionSelectionPrefix_full, executionSelectionPrefix_zero,
      ExecutionContext, HasParameters, HasRawInput, CountsRepresent,
      input, seed, tripleCount, testCost, bodyCost, scanCost, setZero,
      Env.setVar, foundVar, selectedVar, rankVar, orderVar, blowupVar,
      countLenVar, tripleLenVar, budgetVar, sampleTargetVar,
      sampleBitsVar, rawLenVar, countsArray]
  all_goals try omega
  all_goals aesop

/-! ### Counter advancement -/

def incrementTriangleCounts {n : ℕ} (counts : EdgeVariable n → ℕ)
    (triple : ExecutionTriple n) : EdgeVariable n → ℕ :=
  let edgeOne := s(executionFirstVertex triple, executionSecondVertex triple)
  let edgeTwo := s(executionFirstVertex triple, executionThirdVertex triple)
  let edgeThree := s(executionSecondVertex triple, executionThirdVertex triple)
  let afterOne := incrementEdgeCount counts edgeOne
  let afterTwo := if edgeTwo = edgeOne then afterOne
    else incrementEdgeCount afterOne edgeTwo
  if edgeThree = edgeOne then afterTwo
  else if edgeThree = edgeTwo then afterTwo
  else incrementEdgeCount afterTwo edgeThree

lemma incrementTriangleCounts_eq_advance {n : ℕ}
    (counts : EdgeVariable n → ℕ) (triple : ExecutionTriple n) :
    incrementTriangleCounts counts triple =
      advanceExecutionCounts counts (some triple) := by
  classical
  funext edge
  let edgeOne := s(executionFirstVertex triple, executionSecondVertex triple)
  let edgeTwo := s(executionFirstVertex triple, executionThirdVertex triple)
  let edgeThree := s(executionSecondVertex triple, executionThirdVertex triple)
  by_cases h21 : edgeTwo = edgeOne <;>
    by_cases h31 : edgeThree = edgeOne <;>
    by_cases h32 : edgeThree = edgeTwo <;>
    by_cases h1 : edge = edgeOne <;>
    by_cases h2 : edge = edgeTwo <;>
    by_cases h3 : edge = edgeThree <;>
    simp_all [incrementTriangleCounts, incrementEdgeCount,
      advanceExecutionCounts, executionTriangleVariables, edgeOne, edgeTwo,
      edgeThree]

theorem advanceCounters_spec (B : ℕ) {n : ℕ} (input : BitString)
    (counts : EdgeVariable n → ℕ) (selection : Option (ExecutionTriple n))
    (hOneB : 1 < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsSuccB : ∀ edge, counts edge + 1 < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        SelectionRepresent selection state)
      advanceCounters
      (fun _ final => ExecutionContext n input
        (advanceExecutionCounts counts selection) final)
      200 := by
  unfold Spec
  intro initial hstate
  rcases hstate with ⟨hcontext, hselection⟩
  cases selection with
  | none =>
      unfold advanceCounters Com.block
      run_vcg
      all_goals
        simp_all [SelectionRepresent, ExecutionContext,
          advanceExecutionCounts, setZero, setOne, Env.setVar, foundVar]
      all_goals omega
  | some triple =>
      let edgeOne : EdgeVariable n :=
        s(executionFirstVertex triple, executionSecondVertex triple)
      let edgeTwo : EdgeVariable n :=
        s(executionFirstVertex triple, executionThirdVertex triple)
      let edgeThree : EdgeVariable n :=
        s(executionSecondVertex triple, executionThirdVertex triple)
      let countsOne := incrementEdgeCount counts edgeOne
      let stateOne := initial.setArr countsArray (edgeSlot edgeOne)
        (counts edgeOne + 1)
      have hrepOne : CountsRepresent n countsOne stateOne := by
        exact hcontext.2.2.2.increment edgeOne
      let countsTwo := if edgeTwo = edgeOne then countsOne
        else incrementEdgeCount countsOne edgeTwo
      let stateTwo := if edgeTwo = edgeOne then stateOne
        else stateOne.setArr countsArray (edgeSlot edgeTwo) (countsOne edgeTwo + 1)
      have hrepTwo : CountsRepresent n countsTwo stateTwo := by
        dsimp only [countsTwo, stateTwo]
        split
        · exact hrepOne
        · exact hrepOne.increment edgeTwo
      let countsThree := if edgeThree = edgeOne then countsTwo
        else if edgeThree = edgeTwo then countsTwo
        else incrementEdgeCount countsTwo edgeThree
      let stateThree := if edgeThree = edgeOne then stateTwo
        else if edgeThree = edgeTwo then stateTwo
        else stateTwo.setArr countsArray (edgeSlot edgeThree)
          (countsTwo edgeThree + 1)
      have hrepThree : CountsRepresent n countsThree stateThree := by
        dsimp only [countsThree, stateThree]
        split
        · exact hrepTwo
        · split
          · exact hrepTwo
          · exact hrepTwo.increment edgeThree
      have hcountsOne (edge : EdgeVariable n) : countsOne edge ≤ counts edge + 1 := by
        simp [countsOne, incrementEdgeCount]
        split <;> omega
      have hcountsTwo (edge : EdgeVariable n) : countsTwo edge ≤ counts edge + 1 := by
        dsimp only [countsTwo]
        split
        · exact hcountsOne edge
        · simp only [incrementEdgeCount]
          split
          · have hneq : edgeTwo ≠ edgeOne := by assumption
            subst edge
            simp [countsOne, incrementEdgeCount, hneq]
          · exact hcountsOne edge
      have hvalueOne : counts edgeOne + 1 < B := hcountsSuccB edgeOne
      have hvalueTwo (hNe : edgeTwo ≠ edgeOne) :
          countsOne edgeTwo + 1 < B := by
        simpa [countsOne, incrementEdgeCount, hNe] using hcountsSuccB edgeTwo
      have hvalueThree (hNeOne : edgeThree ≠ edgeOne)
          (hNeTwo : edgeThree ≠ edgeTwo) : countsTwo edgeThree + 1 < B := by
        by_cases hEq : edgeTwo = edgeOne
        · simp [countsTwo, hEq, countsOne, incrementEdgeCount, hNeOne]
          exact hcountsSuccB edgeThree
        · simp [countsTwo, hEq, countsOne, incrementEdgeCount, hNeOne,
            hNeTwo]
          exact hcountsSuccB edgeThree
      have hfinalCounts : countsThree = incrementTriangleCounts counts triple := by
        rfl
      have hadvance : countsThree = advanceExecutionCounts counts (some triple) := by
        rw [hfinalCounts, incrementTriangleCounts_eq_advance]
      unfold advanceCounters Com.block
      run_vcg
      all_goals
        simp_all [SelectionRepresent, ExecutionContext, HasParameters,
          CountsRepresent, CountsRepresent.getElem?, edgeOne, edgeTwo,
          edgeThree, countsOne, countsTwo, countsThree, stateOne, stateTwo,
          stateThree, incrementEdgeCount, hadvance, setZero, setOne,
          Env.setVar, foundVar, selectedEdgeOneVar, selectedEdgeTwoVar,
          selectedEdgeThreeVar, countsArray, rawArray]
      all_goals try omega
      all_goals aesop

/-! ### Bounded resampling rounds -/

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
      have hprior := ih
      omega

def RoundInvariant {n : ℕ} (graph : GraphCode n) (seed : ExecutionSeed n)
    (input : BitString) (state : Env) : Prop :=
  state.vars roundVar ≤ executionBudget n ∧
  ExecutionContext n input
    (executeRounds graph seed (state.vars roundVar) (fun _ => 0)).1 state

theorem resamplingRoundBody_spec (B : ℕ) {n : ℕ}
    (graph : GraphCode n) (flatSeed : FlatExecutionSeed n)
    (hn : 0 < n)
    (hB : 2 + n * n + flatRandomBitCount n < B)
    (htripleB : (n * n) * (n * n) * (n * n) + 1 < B)
    (hinputB : (pairBits graph.bits flatSeed.bits).length < B)
    (hvaluesB : ∀ value ∈ pairBits graph.bits flatSeed.bits, value < B)
    (hbudgetB : executionBudget n + 1 < B)
    (hsampleB : executionSampleBits n < B)
    (hcountLenB : (n * n) * (n * n) < B) :
    let seed := executionSeedOfFlat flatSeed
    let input := pairBits graph.bits flatSeed.bits
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
  let input := pairBits graph.bits flatSeed.bits
  let tripleCount := (n * n) * (n * n) * (n * n)
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  let scanBodyCost := testCost + 200
  let scanCost := (scanBodyCost + 4) * tripleCount + 100
  let roundCost := scanCost + 450
  unfold Spec
  intro initial hstate
  rcases hstate with ⟨hinvariant, hround⟩
  let rounds := initial.vars roundVar
  let counts := (executeRounds graph seed rounds (fun _ => 0)).1
  have hcountsLe (edge : EdgeVariable n) : counts edge ≤ rounds := by
    exact executeRounds_zero_counts_le graph seed rounds edge
  have hcountsB (edge : EdgeVariable n) : counts edge < B := by
    have := hcountsLe edge
    omega
  have hcountsSuccB (edge : EdgeVariable n) : counts edge + 1 < B := by
    have := hcountsLe edge
    omega
  have hscan := scanTriples_spec B graph flatSeed counts hn hB htripleB
    hinputB hvaluesB hbudgetB hsampleB hcountLenB hcountsB
  have hadvance := advanceCounters_spec B input counts
    (findExecutionViolation graph seed counts).1 (by omega) hcountLenB
    hcountsSuccB
  unfold Com.block increment
  run_vcg [hscan, hadvance]
  all_goals
    simp_all [RoundInvariant, ExecutionContext, HasParameters, counts, rounds,
      seed, input, tripleCount, testCost, scanBodyCost, scanCost, roundCost,
      executeRounds, Env.setVar, roundVar, SelectionRepresent]
  all_goals try omega
  all_goals aesop
-/

end Lax47Proofs.RamReductionSemantics
