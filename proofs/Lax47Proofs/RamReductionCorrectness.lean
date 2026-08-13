import Lax47Proofs.Redirect

/-!
Correctness and resource bounds for the fixed IMP+ implementation of the
finite Moser--Tardos reduction.  The specifications in this file are about
the actual IMP+ execution relation used by the Lax13 compiler.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionCorrectness

open Lax47.Machine Lax47.Complexity Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

/-- The copied input is retained throughout every reduction phase. -/
def HasRawInput (input : BitString) (state : Env) : Prop :=
  state.vars rawLenVar = input.length ∧ state.arrs rawArray = input

theorem decodeOrder_spec (B : ℕ) (input : BitString) :
    Spec B
      (fun state => HasRawInput input state ∧ input.length < B ∧
        input.getD 1 0 < B ∧ rawOrder input < B ∧ 2 < B)
      decodeOrder
      (fun _ state => HasRawInput input state ∧
        state.vars orderVar = rawOrder input)
      40 := by
  unfold decodeOrder Com.block setZero HasRawInput rawOrder
  run_vcg <;> simp_all [List.getD_eq_getElem?_getD,
    rawLenVar, orderVar, HasRawInput] <;> omega

/-- Scalar parameters materialized before the resampling loops. -/
def HasParameters (n : ℕ) (state : Env) : Prop :=
  state.vars orderVar = n ∧
  state.vars blowupVar = n * n ∧
  state.vars countLenVar = (n * n) * (n * n) ∧
  state.vars tripleLenVar = (n * n) * (n * n) * (n * n) ∧
  state.vars budgetVar = executionBudget n ∧
  state.vars sampleTargetVar = 100 * (n + 1)

theorem computeParameters_spec (B n : ℕ) :
    Spec B
      (fun state => state.vars orderVar = n ∧
        100 * (n + 1) + 1 < B ∧
        12 * (n + 1) ^ 6 < B ∧
        (n * n) * (n * n) * (n * n) < B)
      computeParameters
      (fun _ state => HasParameters n state)
      100 := by
  unfold computeParameters Com.block HasParameters executionBudget
    orderPlusOnePowSix
  run_vcg <;> simp_all [blowupVar, countLenVar, tripleLenVar,
    budgetVar, sampleTargetVar, orderVar] <;> ring_nf at * <;> omega

def SampleLoopInvariant (n : ℕ) (state : Env) : Prop :=
  state.vars sampleTargetVar = 100 * (n + 1) ∧
  state.vars powVar = 2 ^ state.vars sampleBitsVar ∧
  state.vars sampleBitsVar ≤ executionSampleBits n ∧
  state.vars powVar < 2 * (100 * (n + 1) + 1)

lemma sampleCondition_true_lt {B : ℕ} {state : Env}
    (h : (Cond.lt (.var powVar)
      (.add (.var sampleTargetVar) (.lit 1))).evalB B state = some true) :
    state.vars powVar < state.vars sampleTargetVar + 1 := by
  simp only [evalB_condLt_iff, evalB_var_iff, evalB_bin_iff,
    evalB_lit_iff] at h
  obtain ⟨_, _, ⟨rfl, -⟩, ⟨_, _, ⟨rfl, -⟩, ⟨rfl, -⟩,
    rfl, -⟩, htruth⟩ := h
  simpa using htruth.symm

lemma sampleCondition_false_le {B : ℕ} {state : Env}
    (h : (Cond.lt (.var powVar)
      (.add (.var sampleTargetVar) (.lit 1))).evalB B state = some false) :
    state.vars sampleTargetVar + 1 ≤ state.vars powVar := by
  simp only [evalB_condLt_iff, evalB_var_iff, evalB_bin_iff,
    evalB_lit_iff] at h
  obtain ⟨_, _, ⟨rfl, -⟩, ⟨_, _, ⟨rfl, -⟩, ⟨rfl, -⟩,
    rfl, -⟩, htruth⟩ := h
  simp at htruth
  omega

theorem sampleLoop_spec (B n : ℕ)
    (hB : 2 * (100 * (n + 1) + 1) < B)
    (hbitsB : executionSampleBits n + 1 < B) :
    Spec B
      (SampleLoopInvariant n)
      (.while (.lt (.var powVar)
        (.add (.var sampleTargetVar) (.lit 1)))
        (Com.block [
          increment sampleBitsVar,
          .assign powVar (.mul (.var powVar) (.lit 2))]))
      (fun _ state => SampleLoopInvariant n state ∧
        state.vars sampleBitsVar = executionSampleBits n)
      (30 * (executionSampleBits n + 1)) := by
  let condition : Cond := .lt (.var powVar)
    (.add (.var sampleTargetVar) (.lit 1))
  let body : Com := Com.block [
    increment sampleBitsVar,
    .assign powVar (.mul (.var powVar) (.lit 2))]
  let invariant := SampleLoopInvariant n
  let variant : Env → ℕ := fun state =>
    executionSampleBits n - state.vars sampleBitsVar
  have hbodyStrong : Spec B
      (fun state => invariant state ∧
        condition.evalB B state = some true ∧
        state.vars powVar < state.vars sampleTargetVar + 1)
      body
      (fun state state' => invariant state' ∧
        variant state' < variant state)
      20 := by
    dsimp only [body, condition, invariant, variant]
    unfold Com.block increment SampleLoopInvariant
    run_vcg
    all_goals
      simp_all [sampleBitsVar, powVar, sampleTargetVar, Nat.pow_succ]
    all_goals
      have hsample : σ.vars "r.sampleBits" < executionSampleBits n := by
        apply (pow_two_lt_sampleTarget_succ_iff n _).mp
        omega
      ring_nf at *
      omega
  have hbody : Spec B
      (fun state => invariant state ∧
        condition.evalB B state = some true)
      body
      (fun state state' => invariant state' ∧
        variant state' < variant state)
      20 := hbodyStrong.pre (by
        intro state hstate
        exact ⟨hstate.1, hstate.2,
          sampleCondition_true_lt hstate.2⟩)
  have hloop : Spec B (SampleLoopInvariant n)
      (.while condition body)
      (fun _ state => SampleLoopInvariant n state ∧
        condition.evalB B state = some false)
      (30 * (executionSampleBits n + 1)) := by
    apply Spec.while_count invariant variant 20
    · intro state hstate
      rcases hstate with ⟨htarget, hpow, hbits, hpowBound⟩
      dsimp only [condition]
      have hpowB : state.vars powVar < B := by
        omega
      have htargetB : state.vars sampleTargetVar < B := by
        rw [htarget]
        omega
      have honeB : 1 < B := by omega
      have hadd : (Expr.add (.var sampleTargetVar) (.lit 1)).evalB B state =
          some (state.vars sampleTargetVar + 1) := by
        exact evalB_bin (op := .add) (evalB_var htargetB)
          (evalB_lit honeB) (by
            simp only [Bop.apply_add]
            rw [htarget]
            omega)
      exact ⟨_, evalB_condLt (evalB_var hpowB) hadd⟩
    · exact hbody
    · intro state hstate
      exact hstate
    · intro state hstate
      dsimp only [variant, condition]
      simp only [Cond.size, Expr.size]
      omega
  apply hloop.post
  intro initial final hinitial hfinal
  rcases hfinal with ⟨hinvariant, hfalse⟩
  refine ⟨hinvariant, ?_⟩
  rcases hinvariant with ⟨htarget, hpow, hle, -⟩
  have htruth := sampleCondition_false_le hfalse
  by_contra hne
  have hlt : final.vars sampleBitsVar < executionSampleBits n := by omega
  have hp := (pow_two_lt_sampleTarget_succ_iff n _).2 hlt
  rw [htarget, hpow] at htruth
  omega

theorem computeSampleBits_spec (B n : ℕ)
    (hB : 2 * (100 * (n + 1) + 1) < B)
    (hbitsB : executionSampleBits n + 1 < B) :
    Spec B
      (fun state => state.vars sampleTargetVar = 100 * (n + 1))
      computeSampleBits
      (fun _ state => state.vars sampleTargetVar = 100 * (n + 1) ∧
        state.vars sampleBitsVar = executionSampleBits n ∧
        state.vars powVar = 2 ^ executionSampleBits n)
      (30 * (executionSampleBits n + 1) + 20) := by
  have hloop := sampleLoop_spec B n hB hbitsB
  unfold computeSampleBits Com.block setZero
  run_vcg [hloop]
  all_goals
    simp_all [SampleLoopInvariant, sampleBitsVar, powVar, sampleTargetVar] <;>
      omega

/-! ### Reading the copied Boolean word -/

theorem readRawBitVar_spec (B : ℕ) (input : BitString) (indexName : String)
    (destination : String) (position : ℕ)
    (hdestination : destination ≠ rawLenVar) :
    Spec B
      (fun state => HasRawInput input state ∧
        state.vars indexName = position ∧ position < B ∧ input.length < B ∧
        (∀ value ∈ input, value < B) ∧ 1 < B)
      (readRawBit (.var indexName) destination)
      (fun initial final =>
        HasRawInput input final ∧
        final.vars destination = bitWord (rawBit input position) ∧
        (∀ name, name ≠ destination →
          final.vars name = initial.vars name) ∧
        final.arrs = initial.arrs ∧ final.inp = initial.inp ∧
        final.out = initial.out)
      30 := by
  unfold readRawBit setZero setOne HasRawInput rawBit bitWord
  run_vcg <;>
    simp_all [rawLenVar, Env.setVar, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem] <;>
    aesop

/-! ### Arithmetic view of the fixed triple enumeration -/

def tripleAtRank (n rank : ℕ)
    (hrank : rank < (n * n) * (n * n) * (n * n)) : ExecutionTriple n :=
  (executionTripleEquiv n).symm ⟨rank, hrank⟩

lemma tripleAtRank_first_rank (n rank : ℕ)
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    blowupRank (executionFirstVertex (tripleAtRank n rank hrank)) =
      rank / ((n * n) * (n * n)) := by
  unfold tripleAtRank executionTripleEquiv
    executionFirstVertex blowupRank executionVertexEquiv
  simp [finProdFinEquiv]
  exact Nat.mod_add_div _ _

lemma tripleAtRank_second_rank (n rank : ℕ)
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    blowupRank (executionSecondVertex (tripleAtRank n rank hrank)) =
      rank / (n * n) % (n * n) := by
  unfold tripleAtRank executionTripleEquiv executionSecondVertex blowupRank
    executionVertexEquiv
  simp [finProdFinEquiv]
  rw [Nat.mod_add_div]
  exact Nat.mod_mul_right_div_self rank (n * n) (n * n)

lemma tripleAtRank_third_rank (n rank : ℕ)
    (hrank : rank < (n * n) * (n * n) * (n * n)) :
    blowupRank (executionThirdVertex (tripleAtRank n rank hrank)) =
      rank % (n * n) := by
  unfold tripleAtRank executionTripleEquiv executionThirdVertex blowupRank
    executionVertexEquiv
  simp [finProdFinEquiv]
  rw [← Nat.mod_mul_right_mod rank n n]
  exact Nat.mod_add_div (rank % (n * n)) n

lemma blowupRank_div_order {n : ℕ} (hn : 0 < n)
    (vertex : BlowupVertex n) :
    blowupRank vertex / n = vertex.1.1 := by
  rcases vertex with ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
  unfold blowupRank
  simp [finProdFinEquiv]
  rw [Nat.add_mul_div_left]
  simp [Nat.div_eq_of_lt hright, hn]
  exact hn

lemma rawBit_pairBits_graph {n : ℕ} (input : GraphCode n)
    (seed : FlatExecutionSeed n) (left right : Fin n) :
    rawBit (pairBits input.bits seed.bits)
      (2 + left.1 * n + right.1) = input.adjacent left right := by
  unfold rawBit pairBits
  have hget :
      (input.bits.length :: input.bits ++ seed.bits).getD
          (2 + left.1 * n + right.1) 0 =
        input.bits.getD (1 + left.1 * n + right.1) 0 := by
    calc
      (input.bits.length :: input.bits ++ seed.bits).getD
          (2 + left.1 * n + right.1) 0 =
          (input.bits ++ seed.bits).getD
            (1 + left.1 * n + right.1) 0 := by
        rw [show 2 + left.1 * n + right.1 =
          (1 + left.1 * n + right.1) + 1 by omega]
        exact List.getD_cons_succ
      _ = input.bits.getD (1 + left.1 * n + right.1) 0 := by
        apply List.getD_append
        rw [graphCode_bits_length]
        nlinarith [left.2, right.2]
  rw [hget, GraphCode.bits_getD]
  cases input.adjacent left right <;> rfl

lemma rawBit_pairBits_seed {n : ℕ} (input : GraphCode n)
    (seed : FlatExecutionSeed n) (index : Fin (flatRandomBitCount n)) :
    rawBit (pairBits input.bits seed.bits) (2 + n * n + index.1) =
      seed index := by
  have hdecoded := congrFun (rawFlatSeedAt_pairBits input seed) index
  exact hdecoded

def decodedFirstRank (N rank : ℕ) : ℕ := rank / (N * N)
def decodedSecondRank (N rank : ℕ) : ℕ :=
  rank / N - (rank / N / N) * N
def decodedThirdRank (N rank : ℕ) : ℕ := rank - (rank / N) * N

def canonicalSlot (N left right : ℕ) : ℕ :=
  if left < right then left * N + right else right * N + left

lemma decodedSecondRank_eq_mod (N rank : ℕ) :
    decodedSecondRank N rank = rank / N % N := by
  simp [decodedSecondRank, Nat.mod_eq_sub_mul_div, Nat.mul_comm]

lemma decodedThirdRank_eq_mod (N rank : ℕ) :
    decodedThirdRank N rank = rank % N := by
  simp [decodedThirdRank, Nat.mod_eq_sub_mul_div, Nat.mul_comm]

lemma decodedFirstRank_lt {N rank : ℕ} (hN : 0 < N)
    (hrank : rank < N * N * N) : decodedFirstRank N rank < N := by
  rw [decodedFirstRank, Nat.div_lt_iff_lt_mul (by positivity)]
  simpa only [Nat.mul_assoc] using hrank

lemma decodedSecondRank_lt {N rank : ℕ} (hN : 0 < N) :
    decodedSecondRank N rank < N := by
  rw [decodedSecondRank_eq_mod]
  exact Nat.mod_lt _ hN

lemma decodedThirdRank_lt {N rank : ℕ} (hN : 0 < N) :
    decodedThirdRank N rank < N := by
  rw [decodedThirdRank_eq_mod]
  exact Nat.mod_lt _ hN

theorem edgeSlotCom_full_spec (B : ℕ) (left right destination : String) :
    Spec B
      (fun state => state.vars left < B ∧ state.vars right < B ∧
        state.vars blowupVar < B ∧
        state.vars left * state.vars blowupVar + state.vars right < B ∧
        state.vars right * state.vars blowupVar + state.vars left < B)
      (edgeSlotCom left right destination)
      (fun initial final =>
        final.vars destination =
          canonicalSlot (initial.vars blowupVar)
            (initial.vars left) (initial.vars right) ∧
        (∀ name, name ≠ destination →
          final.vars name = initial.vars name) ∧
        final.arrs = initial.arrs ∧ final.inp = initial.inp ∧
        final.out = initial.out)
      20 := by
  unfold edgeSlotCom canonicalSlot
  run_vcg <;> simp_all [Env.setVar] <;> aesop

def HasDecodedRanks (n rank : ℕ) (state : Env) : Prop :=
  state.vars blowupVar = n * n ∧
  state.vars firstVar = decodedFirstRank (n * n) rank ∧
  state.vars secondVar = decodedSecondRank (n * n) rank ∧
  state.vars thirdVar = decodedThirdRank (n * n) rank ∧
  state.vars firstBaseVar = decodedFirstRank (n * n) rank / n ∧
  state.vars secondBaseVar = decodedSecondRank (n * n) rank / n ∧
  state.vars thirdBaseVar = decodedThirdRank (n * n) rank / n

def HasDecodedTriple (n rank : ℕ) (state : Env) : Prop :=
  HasDecodedRanks n rank state ∧
  state.vars edgeOneVar = canonicalSlot (n * n)
    (decodedFirstRank (n * n) rank)
    (decodedSecondRank (n * n) rank) ∧
  state.vars edgeTwoVar = canonicalSlot (n * n)
    (decodedFirstRank (n * n) rank)
    (decodedThirdRank (n * n) rank) ∧
  state.vars edgeThreeVar = canonicalSlot (n * n)
    (decodedSecondRank (n * n) rank)
    (decodedThirdRank (n * n) rank)

theorem decodeTripleRanks_spec (B n rank : ℕ) (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n))
    (hB : (n * n) * (n * n) * (n * n) + 1 < B) :
    Spec B
      (fun state => state.vars orderVar = n ∧
        state.vars blowupVar = n * n ∧
        state.vars rankVar = rank)
      decodeTripleRanks
      (fun _ state => HasDecodedRanks n rank state)
      300 := by
  let N := n * n
  have hNpos : 0 < N := by positivity
  have hfirst : decodedFirstRank N rank < N :=
    decodedFirstRank_lt hNpos (by simpa [N, Nat.mul_assoc] using hrank)
  have hsecond : decodedSecondRank N rank < N :=
    decodedSecondRank_lt hNpos
  have hthird : decodedThirdRank N rank < N :=
    decodedThirdRank_lt hNpos
  have hN2le : N * N ≤ N * N * N := by nlinarith
  have hcube : N * N * N =
      (n * n) * (n * n) * (n * n) := by simp [N]
  have hB' : N * N * N + 1 < B := by simpa [hcube] using hB
  have hNB : N < B := by nlinarith
  have hN2B : N * N < B := by nlinarith
  have hrankB : rank < B := by
    have : rank < N * N * N := by simpa [hcube] using hrank
    omega
  have hquotB : rank / N < B :=
    (Nat.div_le_self rank N).trans_lt hrankB
  have hquotquotB : rank / N / N < B :=
    (Nat.div_le_self (rank / N) N).trans_lt hquotB
  have hquotMul : rank / N / N * N ≤ rank / N :=
    Nat.div_mul_le_self _ _
  have hquotMulB : rank / N / N * N < B := hquotMul.trans_lt hquotB
  have hthirdMul : rank / N * N ≤ rank := Nat.div_mul_le_self _ _
  have hthirdMulB : rank / N * N < B := hthirdMul.trans_lt hrankB
  have hfirstB : decodedFirstRank N rank < B := hfirst.trans hNB
  have hsecondB : decodedSecondRank N rank < B := hsecond.trans hNB
  have hthirdB : decodedThirdRank N rank < B := hthird.trans hNB
  have hbaseFirstB : decodedFirstRank N rank / n < B :=
    (Nat.div_le_self _ _).trans_lt hfirstB
  have hbaseSecondB : decodedSecondRank N rank / n < B :=
    (Nat.div_le_self _ _).trans_lt hsecondB
  have hbaseThirdB : decodedThirdRank N rank / n < B :=
    (Nat.div_le_self _ _).trans_lt hthirdB
  have hNLiteralB : n * n < B := by simpa [N] using hNB
  have hN2LiteralB : (n * n) * (n * n) < B := by
    simpa [N] using hN2B
  have hfirstLiteralB : rank / ((n * n) * (n * n)) < B := by
    simpa [decodedFirstRank, N] using hfirstB
  have hquotLiteralB : rank / (n * n) < B := by
    simpa [N] using hquotB
  have hquotquotLiteralB : rank / (n * n) / (n * n) < B := by
    simpa [N] using hquotquotB
  have hquotMulLiteralB : rank / (n * n) / (n * n) * (n * n) < B := by
    simpa [N] using hquotMulB
  have hsecondLiteralB :
      rank / (n * n) - rank / (n * n) / (n * n) * (n * n) < B := by
    simpa [decodedSecondRank, N] using hsecondB
  have hthirdMulLiteralB : rank / (n * n) * (n * n) < B := by
    simpa [N] using hthirdMulB
  have hthirdLiteralB : rank - rank / (n * n) * (n * n) < B := by
    simpa [decodedThirdRank, N] using hthirdB
  have hbaseFirstLiteralB : rank / ((n * n) * (n * n)) / n < B := by
    simpa [decodedFirstRank, N] using hbaseFirstB
  have hbaseSecondLiteralB :
      (rank / (n * n) - rank / (n * n) / (n * n) * (n * n)) / n < B := by
    simpa [decodedSecondRank, N] using hbaseSecondB
  have hbaseThirdLiteralB : (rank - rank / (n * n) * (n * n)) / n < B := by
    simpa [decodedThirdRank, N] using hbaseThirdB
  unfold decodeTripleRanks Com.block
  unfold Spec
  intro σ hstate
  rcases hstate with ⟨horderState, hblowupState, hrankState⟩
  have horderLiteral := horderState
  have hblowupLiteral := hblowupState
  have hrankLiteral := hrankState
  simp only [orderVar] at horderLiteral
  simp only [blowupVar] at hblowupLiteral
  simp only [rankVar] at hrankLiteral
  have horderStateB : σ.vars orderVar < B := by
    rw [horderState]
    have hnN : n ≤ n * n := by nlinarith
    exact hnN.trans_lt hNLiteralB
  have horderLiteralB : σ.vars "r.n" < B := by
    simpa only [orderVar] using horderStateB
  run_vcg
  all_goals
    simp [HasDecodedRanks, decodedFirstRank, decodedSecondRank,
      decodedThirdRank, orderVar, blowupVar, rankVar, firstVar,
      secondVar, thirdVar, firstBaseVar, secondBaseVar, thirdBaseVar, N,
      horderState, hblowupState, hrankState, horderLiteral,
      hblowupLiteral, hrankLiteral]
  all_goals
    omega

theorem decodeTripleEdges_spec (B n rank : ℕ) (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n))
    (hB : (n * n) * (n * n) + 1 < B) :
    Spec B (HasDecodedRanks n rank) decodeTripleEdges
      (fun _ state => HasDecodedTriple n rank state) 100 := by
  let N := n * n
  have hNpos : 0 < N := by positivity
  have hfirst : decodedFirstRank N rank < N :=
    decodedFirstRank_lt hNpos (by simpa [N, Nat.mul_assoc] using hrank)
  have hsecond : decodedSecondRank N rank < N :=
    decodedSecondRank_lt hNpos
  have hthird : decodedThirdRank N rank < N :=
    decodedThirdRank_lt hNpos
  have hN2 : N * N = (n * n) * (n * n) := by simp [N]
  have hB' : N * N + 1 < B := by simpa [hN2] using hB
  have hNB : N < B := by
    have hNone : 1 ≤ N := hNpos
    calc
      N = N * 1 := by simp
      _ ≤ N * N := Nat.mul_le_mul_left N hNone
      _ < N * N + 1 := by omega
      _ < B := hB'
  have hslot (left right : ℕ) (hleft : left < N) (hright : right < N) :
      canonicalSlot N left right < N * N := by
    unfold canonicalSlot
    split <;> nlinarith
  have hslotOne := hslot _ _ hfirst hsecond
  have hslotTwo := hslot _ _ hfirst hthird
  have hslotThree := hslot _ _ hsecond hthird
  have hpair (left right : ℕ) (hleft : left < N) (hright : right < N) :
      left * N + right < B ∧ right * N + left < B := by
    constructor <;> nlinarith
  have hpairOne := hpair _ _ hfirst hsecond
  have hpairTwo := hpair _ _ hfirst hthird
  have hpairThree := hpair _ _ hsecond hthird
  have slotOne := edgeSlotCom_full_spec B firstVar secondVar edgeOneVar
  have slotTwo := edgeSlotCom_full_spec B firstVar thirdVar edgeTwoVar
  have slotThree := edgeSlotCom_full_spec B secondVar thirdVar edgeThreeVar
  unfold decodeTripleEdges Com.block
  unfold Spec
  intro σ hstate
  rcases hstate with
    ⟨hblowupState, hfirstState, hsecondState, hthirdState,
      hfirstBaseState, hsecondBaseState, hthirdBaseState⟩
  have hblowupLiteral := hblowupState
  have hfirstLiteral := hfirstState
  have hsecondLiteral := hsecondState
  have hthirdLiteral := hthirdState
  simp only [blowupVar] at hblowupLiteral
  simp only [firstVar] at hfirstLiteral
  simp only [secondVar] at hsecondLiteral
  simp only [thirdVar] at hthirdLiteral
  run_vcg [slotOne, slotTwo, slotThree] <;>
    simp_all [HasDecodedRanks, HasDecodedTriple, decodedFirstRank,
      decodedSecondRank, decodedThirdRank, blowupVar, firstVar, secondVar, thirdVar,
      firstBaseVar, secondBaseVar, thirdBaseVar, edgeOneVar, edgeTwoVar,
      edgeThreeVar, N, hblowupLiteral, hfirstLiteral, hsecondLiteral,
      hthirdLiteral] <;>
    omega

theorem decodeTriple_spec (B n rank : ℕ) (hn : 0 < n)
    (hrank : rank < (n * n) * (n * n) * (n * n))
    (hB : (n * n) * (n * n) * (n * n) + 1 < B) :
    Spec B
      (fun state => state.vars orderVar = n ∧
        state.vars blowupVar = n * n ∧
        state.vars rankVar = rank)
      decodeTriple
      (fun _ state => HasDecodedTriple n rank state)
      400 := by
  have hranks := decodeTripleRanks_spec B n rank hn hrank hB
  have hedges := decodeTripleEdges_spec B n rank hn hrank (by
    have hbase : 1 ≤ n * n := by nlinarith [Nat.mul_pos hn hn]
    nlinarith)
  unfold decodeTriple
  exact Spec.seq hranks hedges (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

end Lax47Proofs.RamReductionCorrectness
