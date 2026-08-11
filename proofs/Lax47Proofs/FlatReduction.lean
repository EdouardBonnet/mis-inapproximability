import Lax47Proofs.OperationalReduction

/-!
The finite probability proof uses a structured family of Boolean samples,
whereas a randomized Turing machine receives one flat string of fair bits.
This file gives the uniform, arithmetic reindexing used by the implementation.
The square edge table deliberately contains unused entries below the diagonal;
the reduction reads only the canonical upper-triangular entry.  The ignored
bits remain independent and do not change any probability.
-/

set_option autoImplicit false

namespace Lax47Proofs.FlatReduction

open Lax47.Machine Lax47.Complexity Lax47.Reduction
open Lax47Proofs.FiniteExecution Lax47Proofs.OperationalReduction

/-! ### Total decoding of a machine input

The certified machine is total on arbitrary words.  It therefore caps the
claimed graph order by the actual input length and treats every missing or
non-$1$ entry as false.  On the well-formed words used by the gap solver these
definitions reduce exactly to the supplied graph and flat seed.
-/

/-- Read a Boolean word, with every value except $1$ interpreted as false. -/
def rawBit (input : BitString) (index : ℕ) : Bool :=
  decide (input.getD index 0 = 1)

/-- The graph order used on an arbitrary machine input. -/
def rawOrder (input : BitString) : ℕ :=
  min (input.getD 1 0) input.length

/-- Canonical symmetric graph of a specified order decoded from a word. -/
def rawGraphCodeAt (n : ℕ) (input : BitString) : GraphCode n where
  adjacent := fun left right ↦
    if left = right then false
    else rawBit input (2 + left.1 * n + right.1) &&
      rawBit input (2 + right.1 * n + left.1)
  loopless := by simp
  symmetric := by
    intro left right
    by_cases hEq : left = right
    · simp [hEq]
    · simp [hEq, Ne.symm hEq, Bool.and_comm]

/-- Canonical symmetric graph decoded from an arbitrary word. -/
def rawGraphCode (input : BitString) : GraphCode (rawOrder input) :=
  rawGraphCodeAt (rawOrder input) input

/-- Row-major lookup in the executable graph encoding. -/
lemma GraphCode.bits_getD {n : ℕ} (input : GraphCode n)
    (left right : Fin n) :
    input.bits.getD (1 + left.1 * n + right.1) 0 =
      bitWord (input.adjacent left right) := by
  unfold GraphCode.bits
  rw [show 1 + left.1 * n + right.1 =
    (left.1 * n + right.1) + 1 by omega]
  simp only [List.getD_cons_succ]
  rw [List.getD_eq_getElem]
  · rw [List.getElem_ofFn]
    have hrank :
        (⟨left.1 * n + right.1, by nlinarith [left.2, right.2]⟩ :
            Fin (n * n)) = finProdFinEquiv (left, right) := by
      apply Fin.ext
      simp [finProdFinEquiv]
      ring
    change bitWord (input.adjacent
      (finProdFinEquiv.symm
        (⟨left.1 * n + right.1, by nlinarith [left.2, right.2]⟩ :
          Fin (n * n))).1
      (finProdFinEquiv.symm
        (⟨left.1 * n + right.1, by nlinarith [left.2, right.2]⟩ :
          Fin (n * n))).2) = _
    rw [hrank, Equiv.symm_apply_apply]
  · simp
    nlinarith [left.2, right.2]

/-- Number of vertices in the $n$-by-$n$ blow-up. -/
def blowupOrder (n : ℕ) : ℕ := n * n

/-- Rank of a blow-up vertex in the row-major pair encoding. -/
def blowupRank {n : ℕ} (vertex : BlowupVertex n) : ℕ :=
  (finProdFinEquiv vertex : Fin (n * n)).1

lemma blowupRank_lt {n : ℕ} (vertex : BlowupVertex n) :
    blowupRank vertex < blowupOrder n := by
  exact (finProdFinEquiv vertex).2

lemma blowupRank_injective {n : ℕ} :
    Function.Injective (@blowupRank n) := by
  intro left right h
  apply finProdFinEquiv.injective
  exact Fin.ext h

/-- Canonically ordered endpoint ranks of an unordered blow-up edge. -/
def canonicalEdgePair {n : ℕ} (edge : EdgeVariable n) :
    Fin (blowupOrder n) × Fin (blowupOrder n) :=
  Sym2.lift ⟨fun left right ↦
    (⟨min (blowupRank left) (blowupRank right),
        lt_of_le_of_lt (min_le_left _ _) (blowupRank_lt left)⟩,
      ⟨max (blowupRank left) (blowupRank right),
        max_lt (blowupRank_lt left) (blowupRank_lt right)⟩), by
        intro left right
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [min_comm, max_comm]⟩ edge

/-- Canonical square-table slot of an unordered blow-up edge. -/
def edgeSlot {n : ℕ} (edge : EdgeVariable n) : ℕ :=
  (finProdFinEquiv (canonicalEdgePair edge)).1

lemma edgeSlot_mk {n : ℕ} (left right : BlowupVertex n) :
    edgeSlot s(left, right) =
      min (blowupRank left) (blowupRank right) * blowupOrder n +
        max (blowupRank left) (blowupRank right) := by
  simp [edgeSlot, canonicalEdgePair, finProdFinEquiv, Nat.mul_comm,
    Nat.add_comm]

lemma edgeSlot_lt {n : ℕ} (edge : EdgeVariable n) :
    edgeSlot edge < blowupOrder n * blowupOrder n := by
  exact (finProdFinEquiv (canonicalEdgePair edge)).2

lemma edgeSlot_injective {n : ℕ} :
    Function.Injective (@edgeSlot n) := by
  intro left right hslot
  have hcanonical : canonicalEdgePair left = canonicalEdgePair right := by
    apply finProdFinEquiv.injective
    exact Fin.ext hslot
  induction left using Sym2.inductionOn with
  | _ a b =>
      induction right using Sym2.inductionOn with
      | _ c d =>
          have hpair := congrArg
            (fun pair : Fin (blowupOrder n) × Fin (blowupOrder n) ↦
              (pair.1.1, pair.2.1)) hcanonical
          have hmin := congrArg Prod.fst hpair
          have hmax := congrArg Prod.snd hpair
          simp only [canonicalEdgePair, Sym2.lift_mk] at hmin hmax
          rcases le_total (blowupRank a) (blowupRank b) with hab | hba <;>
            rcases le_total (blowupRank c) (blowupRank d) with hcd | hdc
          · simp only [min_eq_left hab, max_eq_right hab,
              min_eq_left hcd, max_eq_right hcd] at hmin hmax
            exact Sym2.eq_iff.mpr (Or.inl
              ⟨blowupRank_injective hmin, blowupRank_injective hmax⟩)
          · simp only [min_eq_left hab, max_eq_right hab,
              min_eq_right hdc, max_eq_left hdc] at hmin hmax
            exact Sym2.eq_iff.mpr (Or.inr
              ⟨blowupRank_injective hmin, blowupRank_injective hmax⟩)
          · simp only [min_eq_right hba, max_eq_left hba,
              min_eq_left hcd, max_eq_right hcd] at hmin hmax
            exact Sym2.eq_iff.mpr (Or.inr
              ⟨blowupRank_injective hmax, blowupRank_injective hmin⟩)
          · simp only [min_eq_right hba, max_eq_left hba,
              min_eq_right hdc, max_eq_left hdc] at hmin hmax
            exact Sym2.eq_iff.mpr (Or.inl
              ⟨blowupRank_injective hmax, blowupRank_injective hmin⟩)

/-- Length of the padded flat random tape. -/
def flatRandomBitCount (n : ℕ) : ℕ :=
  blowupOrder n * blowupOrder n * (executionBudget n + 1) *
    executionSampleBits n

/-- A standard flat tape of independent fair bits. -/
abbrev FlatExecutionSeed (n : ℕ) := RandomSeed (flatRandomBitCount n)

/-- A paired well-formed graph word recovers its advertised order. -/
lemma rawOrder_pairBits {n r : ℕ} (input : GraphCode n)
    (seed : RandomSeed r) :
    rawOrder (pairBits input.bits seed.bits) = n := by
  unfold rawOrder pairBits
  have hget :
      (input.bits.length :: input.bits ++ seed.bits).getD 1 0 =
        (input.bits ++ seed.bits).getD 0 0 := by
    simpa only [Nat.zero_add] using
      (List.getD_cons_succ (x := input.bits.length)
        (xs := input.bits ++ seed.bits) (n := 0) (d := 0))
  rw [hget]
  rw [List.getD_append input.bits seed.bits 0 0 (by
    rw [GraphCode.bits_length]
    omega)]
  simp [GraphCode.bits]
  nlinarith

/-- Lookup in the fixed-length word encoding of a random tape. -/
lemma RandomSeed.bits_getD {r : ℕ} (seed : RandomSeed r)
    (index : Fin r) :
    seed.bits.getD index.1 0 = bitWord (seed index) := by
  unfold RandomSeed.bits
  rw [List.getD_eq_getElem]
  · rw [List.getElem_map, List.getElem_ofFn]
  · simp

/-- A well-formed paired word decodes to its original graph. -/
lemma rawGraphCodeAt_pairBits {n r : ℕ} (input : GraphCode n)
    (seed : RandomSeed r) :
    rawGraphCodeAt n (pairBits input.bits seed.bits) = input := by
  rw [GraphCode.mk.injEq]
  funext left right
  unfold rawGraphCodeAt
  dsimp only
  by_cases hEq : left = right
  · subst right
    simp [input.loopless]
  · simp only [hEq, ↓reduceIte]
    have hget (a b : Fin n) :
        (pairBits input.bits seed.bits).getD
            (2 + a.1 * n + b.1) 0 =
          input.bits.getD (1 + a.1 * n + b.1) 0 := by
      unfold pairBits
      calc
        (input.bits.length :: input.bits ++ seed.bits).getD
            (2 + a.1 * n + b.1) 0 =
            (input.bits ++ seed.bits).getD
              (1 + a.1 * n + b.1) 0 := by
          rw [show 2 + a.1 * n + b.1 =
            (1 + a.1 * n + b.1) + 1 by omega]
          exact List.getD_cons_succ
        _ = input.bits.getD (1 + a.1 * n + b.1) 0 := by
          apply List.getD_append
          rw [GraphCode.bits_length]
          nlinarith [a.2, b.2]
    unfold rawBit
    rw [hget left right, hget right left,
      GraphCode.bits_getD, GraphCode.bits_getD, input.symmetric]
    cases input.adjacent right left <;> rfl

/-- Position of one structured table bit in the flat random tape. -/
def flatBitIndex {n : ℕ} (edge : EdgeVariable n)
    (row : Fin (executionBudget n + 1))
    (bit : Fin (executionSampleBits n)) : Fin (flatRandomBitCount n) :=
  ⟨(edgeSlot edge * (executionBudget n + 1) + row.1) *
      executionSampleBits n + bit.1, by
    have hedge := edgeSlot_lt edge
    have hrow := row.2
    have hbit := bit.2
    have hrowBlock :
        edgeSlot edge * (executionBudget n + 1) + row.1 <
          (blowupOrder n * blowupOrder n) * (executionBudget n + 1) := by
      calc
        edgeSlot edge * (executionBudget n + 1) + row.1 <
            edgeSlot edge * (executionBudget n + 1) +
              (executionBudget n + 1) := Nat.add_lt_add_left hrow _
        _ = (edgeSlot edge + 1) * (executionBudget n + 1) := by ring
        _ ≤ (blowupOrder n * blowupOrder n) *
              (executionBudget n + 1) := by
          exact Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hedge)
    have hbitBlock :
        (edgeSlot edge * (executionBudget n + 1) + row.1) *
              executionSampleBits n + bit.1 <
          ((blowupOrder n * blowupOrder n) * (executionBudget n + 1)) *
              executionSampleBits n := by
      calc
        (edgeSlot edge * (executionBudget n + 1) + row.1) *
              executionSampleBits n + bit.1 <
            (edgeSlot edge * (executionBudget n + 1) + row.1) *
                executionSampleBits n + executionSampleBits n :=
          Nat.add_lt_add_left hbit _
        _ = (edgeSlot edge * (executionBudget n + 1) + row.1 + 1) *
              executionSampleBits n := by ring
        _ ≤ ((blowupOrder n * blowupOrder n) *
              (executionBudget n + 1)) * executionSampleBits n := by
          exact Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hrowBlock)
    unfold flatRandomBitCount
    simpa only [Nat.mul_assoc] using hbitBlock⟩

/-- Restrict a flat random tape to the cells read by the reduction. -/
def executionSeedOfFlat {n : ℕ} (seed : FlatExecutionSeed n) :
    ExecutionSeed n :=
  fun edge row bit ↦ seed (flatBitIndex edge row bit)

@[simp] lemma executionSeedOfFlat_apply {n : ℕ}
    (seed : FlatExecutionSeed n) (edge : EdgeVariable n)
    (row : Fin (executionBudget n + 1))
    (bit : Fin (executionSampleBits n)) :
    executionSeedOfFlat seed edge row bit = seed (flatBitIndex edge row bit) :=
  rfl

/-- Flat random tape of a specified order decoded after its adjacency matrix. -/
def rawFlatSeedAt (n : ℕ) (input : BitString) : FlatExecutionSeed n :=
  fun index ↦ rawBit input
    (2 + n * n + index.1)

/-- Flat random tape decoded after the adjacency matrix of an arbitrary word. -/
def rawFlatSeed (input : BitString) : FlatExecutionSeed (rawOrder input) :=
  rawFlatSeedAt (rawOrder input) input

/-- A well-formed paired word decodes to its original random tape. -/
lemma rawFlatSeedAt_pairBits {n : ℕ} (input : GraphCode n)
    (seed : FlatExecutionSeed n) :
    rawFlatSeedAt n (pairBits input.bits seed.bits) = seed := by
  funext index
  unfold rawFlatSeedAt rawBit pairBits
  have hget :
      (input.bits.length :: input.bits ++ seed.bits).getD
          (2 + n * n + index.1) 0 =
        (input.bits ++ seed.bits).getD (1 + n * n + index.1) 0 := by
    rw [show 2 + n * n + index.1 =
      (1 + n * n + index.1) + 1 by omega]
    exact List.getD_cons_succ
  rw [hget]
  rw [List.getD_append_right]
  · rw [GraphCode.bits_length]
    simp only [Nat.add_sub_cancel_left]
    rw [RandomSeed.bits_getD]
    cases seed index <;> rfl
  · rw [GraphCode.bits_length]
    omega

/-- A machine word models a graph and flat random tape when the raw decoder
recovers exactly those two semantic objects.  This relation is shared by
canonical graph/seed pairs and by the total decoder on arbitrary words. -/
structure ModelsReductionInput {n : ℕ} (input : BitString)
    (graph : GraphCode n) (seed : FlatExecutionSeed n) : Prop where
  graph_eq : rawGraphCodeAt n input = graph
  seed_eq : rawFlatSeedAt n input = seed

lemma ModelsReductionInput.pairBits {n : ℕ} (graph : GraphCode n)
    (seed : FlatExecutionSeed n) :
    ModelsReductionInput (pairBits graph.bits seed.bits) graph seed := by
  exact ⟨rawGraphCodeAt_pairBits graph seed,
    rawFlatSeedAt_pairBits graph seed⟩

lemma ModelsReductionInput.raw (n : ℕ) (input : BitString) :
    ModelsReductionInput input (rawGraphCodeAt n input)
      (rawFlatSeedAt n input) := by
  exact ⟨rfl, rfl⟩

lemma ModelsReductionInput.seed_bit {n : ℕ} {input : BitString}
    {graph : GraphCode n} {seed : FlatExecutionSeed n}
    (model : ModelsReductionInput input graph seed)
    (index : Fin (flatRandomBitCount n)) :
    rawBit input (2 + n * n + index.1) = seed index := by
  have := congrFun model.seed_eq index
  simpa [rawFlatSeedAt] using this

/-- The total graph word produced by the randomized reduction. -/
def rawReductionGraphBits (input : BitString) : BitString :=
  (executionOutput (rawGraphCode input)
    (executionSeedOfFlat (rawFlatSeed input))).bits

/-- On a well-formed graph/seed pair, the total word function is exactly the
finite Moser--Tardos execution used in the probability proof. -/
lemma rawReductionGraphBits_pairBits {n : ℕ} (input : GraphCode n)
    (seed : FlatExecutionSeed n) :
    rawReductionGraphBits (pairBits input.bits seed.bits) =
      (executionOutput input (executionSeedOfFlat seed)).bits := by
  unfold rawReductionGraphBits rawGraphCode rawFlatSeed
  rw [rawOrder_pairBits input seed]
  rw [rawGraphCodeAt_pairBits, rawFlatSeedAt_pairBits]

/-- The structured coordinate type underlying $ExecutionSeed$. -/
abbrev ExecutionBitIndex (n : ℕ) :=
  (EdgeVariable n × Fin (executionBudget n + 1)) ×
    Fin (executionSampleBits n)

/-- Mixed-radix flattening is an embedding of structured coordinates. -/
def flatBitEmbedding (n : ℕ) :
    ExecutionBitIndex n ↪ Fin (flatRandomBitCount n) where
  toFun index := flatBitIndex index.1.1 index.1.2 index.2
  inj' := by
    rintro ⟨⟨edge, row⟩, bit⟩ ⟨⟨edge', row'⟩, bit'⟩ h
    let edgeFin : Fin (blowupOrder n * blowupOrder n) :=
      ⟨edgeSlot edge, edgeSlot_lt edge⟩
    let edgeFin' : Fin (blowupOrder n * blowupOrder n) :=
      ⟨edgeSlot edge', edgeSlot_lt edge'⟩
    let prefixIndex : Fin ((blowupOrder n * blowupOrder n) *
        (executionBudget n + 1)) := finProdFinEquiv (edgeFin, row)
    let prefixIndex' : Fin ((blowupOrder n * blowupOrder n) *
        (executionBudget n + 1)) := finProdFinEquiv (edgeFin', row')
    have hencoded : finProdFinEquiv (prefixIndex, bit) =
        finProdFinEquiv (prefixIndex', bit') := by
      apply Fin.ext
      have hvalue := congrArg Fin.val h
      simp only [prefixIndex, prefixIndex', edgeFin, edgeFin',
        finProdFinEquiv_apply_val]
      change bit.1 + executionSampleBits n *
          (row.1 + (executionBudget n + 1) * edgeSlot edge) =
        bit'.1 + executionSampleBits n *
          (row'.1 + (executionBudget n + 1) * edgeSlot edge')
      calc
        bit.1 + executionSampleBits n *
              (row.1 + (executionBudget n + 1) * edgeSlot edge) =
            (edgeSlot edge * (executionBudget n + 1) + row.1) *
              executionSampleBits n + bit.1 := by ring
        _ = (edgeSlot edge' * (executionBudget n + 1) + row'.1) *
              executionSampleBits n + bit'.1 := by
          simpa only [flatBitIndex] using hvalue
        _ = bit'.1 + executionSampleBits n *
            (row'.1 + (executionBudget n + 1) * edgeSlot edge') := by ring
    have houter := finProdFinEquiv.injective hencoded
    have hprefix : prefixIndex = prefixIndex' := congrArg Prod.fst houter
    have hbit : bit = bit' := congrArg Prod.snd houter
    have hinner := finProdFinEquiv.injective hprefix
    have hedgeFin : edgeFin = edgeFin' := congrArg Prod.fst hinner
    have hrow : row = row' := congrArg Prod.snd hinner
    have hedge : edge = edge' := edgeSlot_injective (Fin.mk.inj hedgeFin)
    subst edge'
    subst row'
    subst bit'
    rfl

@[simp] lemma flatBitEmbedding_apply (n : ℕ) (index : ExecutionBitIndex n) :
    flatBitEmbedding n index =
      flatBitIndex index.1.1 index.1.2 index.2 :=
  rfl

/-! ### Uniformity of restriction to the used coordinates -/

/-- Coordinates outside the range of an embedding. -/
abbrev EmbeddingComplement {A B : Type} (embedding : A ↪ B) :=
  {value : B // value ∉ Set.range embedding}

/-- An embedding and the complement of its range partition the codomain. -/
noncomputable def embeddingSumEquiv {A B : Type} [Fintype A]
    [DecidableEq B] (embedding : A ↪ B) :
    A ⊕ EmbeddingComplement embedding ≃ B :=
  (Equiv.sumCongr embedding.toEquivRange
      (Equiv.refl (EmbeddingComplement embedding))).trans
    (Equiv.sumCompl (fun value : B ↦ value ∈ Set.range embedding))

/-- A Boolean family splits into its used coordinates and unused coordinates. -/
noncomputable def splitBooleanFamilyEquiv {A B : Type} [Fintype A]
    [DecidableEq B] (embedding : A ↪ B) :
    (B → Bool) ≃ (A → Bool) × (EmbeddingComplement embedding → Bool) :=
  (Equiv.arrowCongr (embeddingSumEquiv embedding) (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow A (EmbeddingComplement embedding) Bool)

@[simp] lemma splitBooleanFamilyEquiv_fst {A B : Type} [Fintype A]
    [DecidableEq B] (embedding : A ↪ B) (family : B → Bool) (index : A) :
    (splitBooleanFamilyEquiv embedding family).1 index = family (embedding index) := by
  classical
  simp [splitBooleanFamilyEquiv, embeddingSumEquiv]

/-- Curry the structured coordinate family used by $ExecutionSeed$. -/
def executionSeedBitsEquiv (n : ℕ) :
    ExecutionSeed n ≃ (ExecutionBitIndex n → Bool) where
  toFun seed index := seed index.1.1 index.1.2 index.2
  invFun bits edge row bit := bits ((edge, row), bit)
  left_inv seed := rfl
  right_inv bits := rfl

/-- A flat fair-bit tape is exactly a structured execution seed plus unused bits. -/
noncomputable def flatSeedSplitEquiv (n : ℕ) :
    FlatExecutionSeed n ≃
      ExecutionSeed n × (EmbeddingComplement (flatBitEmbedding n) → Bool) :=
  (splitBooleanFamilyEquiv (flatBitEmbedding n)).trans
    (Equiv.prodCongr (executionSeedBitsEquiv n).symm
      (Equiv.refl (EmbeddingComplement (flatBitEmbedding n) → Bool)))

@[simp] lemma flatSeedSplitEquiv_fst (n : ℕ) (seed : FlatExecutionSeed n) :
    (flatSeedSplitEquiv n seed).1 = executionSeedOfFlat seed := by
  classical
  funext edge row bit
  change (splitBooleanFamilyEquiv (flatBitEmbedding n) seed).1
      ((edge, row), bit) = seed (flatBitIndex edge row bit)
  rw [splitBooleanFamilyEquiv_fst]
  rfl

lemma filter_card_equiv {A B : Type} [Fintype A] [Fintype B]
    (equiv : A ≃ B) (predicate : B → Prop) [DecidablePred predicate] :
    ((Finset.univ : Finset A).filter fun value ↦ predicate (equiv value)).card =
      ((Finset.univ : Finset B).filter predicate).card := by
  classical
  have hcard := Fintype.card_congr
    (equiv.subtypeEquiv (p := fun value ↦ predicate (equiv value))
      (q := predicate) (fun _ ↦ Iff.rfl))
  simpa only [Fintype.card_subtype, Finset.setOf_mem, Finset.card_univ] using hcard

lemma filter_product_fst_card {A B : Type} [Fintype A] [Fintype B]
    (predicate : A → Prop) [DecidablePred predicate] :
    ((Finset.univ : Finset (A × B)).filter
        (fun pair ↦ predicate pair.1)).card =
      ((Finset.univ : Finset A).filter predicate).card * Fintype.card B := by
  classical
  let equiv : {pair : A × B // predicate pair.1} ≃
      {value : A // predicate value} × B :=
    { toFun := fun pair ↦ (⟨pair.1.1, pair.2⟩, pair.1.2)
      invFun := fun pair ↦ ⟨(pair.1.1, pair.2), pair.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcard := Fintype.card_congr equiv
  simpa only [Fintype.card_subtype, Finset.setOf_mem, Finset.card_univ,
    Fintype.card_prod] using hcard

/-- Every event depending only on the used bits has a constant-size fibre. -/
lemma flat_filter_card (n : ℕ) (predicate : ExecutionSeed n → Prop)
    [DecidablePred predicate] :
    ((Finset.univ : Finset (FlatExecutionSeed n)).filter
        (fun seed ↦ predicate (executionSeedOfFlat seed))).card =
      ((Finset.univ : Finset (ExecutionSeed n)).filter predicate).card *
        Fintype.card (EmbeddingComplement (flatBitEmbedding n) → Bool) := by
  classical
  have hsplit := filter_card_equiv (flatSeedSplitEquiv n)
    (fun pair : ExecutionSeed n ×
      (EmbeddingComplement (flatBitEmbedding n) → Bool) ↦ predicate pair.1)
  rw [filter_product_fst_card] at hsplit
  simpa only [flatSeedSplitEquiv_fst] using hsplit

lemma card_flatExecutionSeed (n : ℕ) :
    Fintype.card (FlatExecutionSeed n) =
      Fintype.card (ExecutionSeed n) *
        Fintype.card (EmbeddingComplement (flatBitEmbedding n) → Bool) := by
  classical
  simpa only [Fintype.card_prod] using Fintype.card_congr (flatSeedSplitEquiv n)

/-- A one-third failure bound transfers exactly to the standard flat tape. -/
lemma flat_failure_card_le_third (n : ℕ)
    (predicate : ExecutionSeed n → Prop) [DecidablePred predicate]
    (hfailure : 3 * ((Finset.univ : Finset (ExecutionSeed n)).filter
      predicate).card ≤ (Finset.univ : Finset (ExecutionSeed n)).card) :
    3 * ((Finset.univ : Finset (FlatExecutionSeed n)).filter
        (fun seed ↦ predicate (executionSeedOfFlat seed))).card ≤
      (Finset.univ : Finset (FlatExecutionSeed n)).card := by
  classical
  rw [flat_filter_card, Finset.card_univ, card_flatExecutionSeed]
  rw [Finset.card_univ] at hfailure
  calc
    3 * (((Finset.univ : Finset (ExecutionSeed n)).filter predicate).card *
          Fintype.card (EmbeddingComplement (flatBitEmbedding n) → Bool)) =
        (3 * ((Finset.univ : Finset (ExecutionSeed n)).filter predicate).card) *
          Fintype.card (EmbeddingComplement (flatBitEmbedding n) → Bool) := by ring
    _ ≤ Fintype.card (ExecutionSeed n) *
          Fintype.card (EmbeddingComplement (flatBitEmbedding n) → Bool) :=
      Nat.mul_le_mul_right _ hfailure

/-- The padded random tape still has polynomial length. -/
lemma flatRandomBitCount_polynomial (n : ℕ) :
    flatRandomBitCount n ≤ 1400 * (n + 1) ^ 12 := by
  have horder : blowupOrder n ≤ (n + 1) ^ 2 := by
    unfold blowupOrder
    nlinarith
  have hbudget : executionBudget n + 1 ≤ 13 * (n + 1) ^ 6 := by
    unfold executionBudget
    have hbase : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have hbits : executionSampleBits n ≤ 101 * (n + 1) := by
    simpa only [executionSampleBits] using sampleBits_le_linear n
  unfold flatRandomBitCount
  calc
    blowupOrder n * blowupOrder n * (executionBudget n + 1) *
          executionSampleBits n ≤
        (n + 1) ^ 2 * (n + 1) ^ 2 * (13 * (n + 1) ^ 6) *
          (101 * (n + 1)) := by gcongr
    _ = 1313 * (n + 1) ^ 11 := by ring
    _ ≤ 1400 * (n + 1) ^ 12 := by
      have hbase : 1 ≤ n + 1 := by omega
      nlinarith [pow_le_pow_right₀ hbase (by omega : 11 ≤ 12)]

/-! ### Uniform monomial padding for the Håstad-gap interface -/

/-- The exact fixed monomial tape length exposed by the gap program. -/
abbrev PolynomialExecutionSeed (n : ℕ) :=
  RandomSeed (polynomialBound 1400 12 n)

/-- Embed the reduction's used flat tape into its fixed polynomial padding. -/
def flatToPolynomialEmbedding (n : ℕ) :
    Fin (flatRandomBitCount n) ↪ Fin (polynomialBound 1400 12 n) where
  toFun index := ⟨index.1, index.2.trans_le (by
    simpa [polynomialBound] using flatRandomBitCount_polynomial n)⟩
  inj' := by
    intro left right equality
    apply Fin.ext
    exact Fin.mk.inj equality

/-- Discard the uniform padding and retain the prefix read by the reduction. -/
def flatSeedOfPolynomial {n : ℕ} (seed : PolynomialExecutionSeed n) :
    FlatExecutionSeed n :=
  fun index ↦ seed (flatToPolynomialEmbedding n index)

@[simp] lemma flatSeedOfPolynomial_apply {n : ℕ}
    (seed : PolynomialExecutionSeed n) (index : Fin (flatRandomBitCount n)) :
    flatSeedOfPolynomial seed index =
      seed (flatToPolynomialEmbedding n index) :=
  rfl

/-- Pairing a graph with the fixed polynomial tape recovers its used prefix. -/
lemma rawFlatSeedAt_pairBits_polynomial {n : ℕ} (input : GraphCode n)
    (seed : PolynomialExecutionSeed n) :
    rawFlatSeedAt n (pairBits input.bits seed.bits) =
      flatSeedOfPolynomial seed := by
  funext index
  unfold rawFlatSeedAt rawBit pairBits
  have hget :
      (input.bits.length :: input.bits ++ seed.bits).getD
          (2 + n * n + index.1) 0 =
        (input.bits ++ seed.bits).getD (1 + n * n + index.1) 0 := by
    rw [show 2 + n * n + index.1 =
      (1 + n * n + index.1) + 1 by omega]
    exact List.getD_cons_succ
  rw [hget]
  rw [List.getD_append_right]
  · rw [GraphCode.bits_length]
    simp only [Nat.add_sub_cancel_left]
    change decide
        (seed.bits.getD (flatToPolynomialEmbedding n index).1 0 = 1) =
      seed (flatToPolynomialEmbedding n index)
    rw [RandomSeed.bits_getD]
    cases seed (flatToPolynomialEmbedding n index) <;> rfl
  · rw [GraphCode.bits_length]
    omega

/-- A polynomially padded Boolean family splits into its prefix and unused bits. -/
noncomputable def polynomialSeedSplitEquiv (n : ℕ) :
    PolynomialExecutionSeed n ≃
      FlatExecutionSeed n ×
        (EmbeddingComplement (flatToPolynomialEmbedding n) → Bool) :=
  splitBooleanFamilyEquiv (flatToPolynomialEmbedding n)

@[simp] lemma polynomialSeedSplitEquiv_fst (n : ℕ)
    (seed : PolynomialExecutionSeed n) :
    (polynomialSeedSplitEquiv n seed).1 = flatSeedOfPolynomial seed := by
  classical
  funext index
  change (splitBooleanFamilyEquiv (flatToPolynomialEmbedding n) seed).1 index =
    seed (flatToPolynomialEmbedding n index)
  rw [splitBooleanFamilyEquiv_fst]

lemma polynomial_filter_card (n : ℕ)
    (predicate : FlatExecutionSeed n → Prop) [DecidablePred predicate] :
    ((Finset.univ : Finset (PolynomialExecutionSeed n)).filter
        (fun seed ↦ predicate (flatSeedOfPolynomial seed))).card =
      ((Finset.univ : Finset (FlatExecutionSeed n)).filter predicate).card *
        Fintype.card
          (EmbeddingComplement (flatToPolynomialEmbedding n) → Bool) := by
  classical
  have hsplit := filter_card_equiv (polynomialSeedSplitEquiv n)
    (fun pair : FlatExecutionSeed n ×
      (EmbeddingComplement (flatToPolynomialEmbedding n) → Bool) ↦
        predicate pair.1)
  rw [filter_product_fst_card] at hsplit
  simpa only [polynomialSeedSplitEquiv_fst] using hsplit

lemma card_polynomialExecutionSeed (n : ℕ) :
    Fintype.card (PolynomialExecutionSeed n) =
      Fintype.card (FlatExecutionSeed n) *
        Fintype.card
          (EmbeddingComplement (flatToPolynomialEmbedding n) → Bool) := by
  classical
  simpa only [Fintype.card_prod] using
    Fintype.card_congr (polynomialSeedSplitEquiv n)

/-- A one-third bound is unchanged by the exact uniform monomial padding. -/
lemma polynomial_failure_card_le_third (n : ℕ)
    (predicate : FlatExecutionSeed n → Prop) [DecidablePred predicate]
    (hfailure : 3 * ((Finset.univ : Finset (FlatExecutionSeed n)).filter
      predicate).card ≤ (Finset.univ : Finset (FlatExecutionSeed n)).card) :
    3 * ((Finset.univ : Finset (PolynomialExecutionSeed n)).filter
        (fun seed ↦ predicate (flatSeedOfPolynomial seed))).card ≤
      (Finset.univ : Finset (PolynomialExecutionSeed n)).card := by
  classical
  rw [polynomial_filter_card, Finset.card_univ,
    card_polynomialExecutionSeed]
  rw [Finset.card_univ] at hfailure
  calc
    3 * (((Finset.univ : Finset (FlatExecutionSeed n)).filter predicate).card *
          Fintype.card
            (EmbeddingComplement (flatToPolynomialEmbedding n) → Bool)) =
        (3 * ((Finset.univ : Finset (FlatExecutionSeed n)).filter
          predicate).card) *
          Fintype.card
            (EmbeddingComplement (flatToPolynomialEmbedding n) → Bool) := by ring
    _ ≤ Fintype.card (FlatExecutionSeed n) *
          Fintype.card
            (EmbeddingComplement (flatToPolynomialEmbedding n) → Bool) :=
      Nat.mul_le_mul_right _ hfailure

end Lax47Proofs.FlatReduction
