import Lax47Proofs.Construction
import Mathlib.Probability.Distributions.Uniform

/-!
The Moser--Tardos theorems analyze an infinite product table, but the actual
reduction reads only a polynomial prefix.  This module proves that dependency,
realizes every Bernoulli cell by a finite block of uniform bits, and transfers
the infinite-product soundness estimate to the resulting finite uniform seed
space.  The infinite table is therefore only an analysis device and is not the
randomness supplied to the gap algorithm.
-/

set_option autoImplicit false

namespace Lax47Proofs.FiniteExecution

open scoped BigOperators ENNReal
open Lax47Proofs.Reduction
open Lax41.MoserTardosDefinitions
open Lax47Proofs.Construction

/-- The edge-table cells with row at most the resampling cutoff. -/
def prefixIndices (n : ℕ) :
    Finset (TableIndex (Variable := EdgeVariable n)) :=
  (Finset.univ : Finset (EdgeVariable n)).sigma fun _ ↦
    Finset.range (cutoffBudget n + 1)

@[simp] lemma mem_prefixIndices {n : ℕ}
    (j : TableIndex (Variable := EdgeVariable n)) :
    j ∈ prefixIndices n ↔ j.2 < cutoffBudget n + 1 := by
  simp [prefixIndices]

/-- Two infinite tables agree through a specified row. -/
def TablesAgreeThrough {n : ℕ} (B : ℕ)
    (left right : SampleTable n) : Prop :=
  ∀ e r, r ≤ B → left ⟨e, r⟩ = right ⟨e, r⟩

/-- After round $t$, no edge counter is larger than $t$. -/
lemma runCounts_le_round {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) (round : ℕ) (e : EdgeVariable n) :
    runCounts (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table round e ≤ round := by
  classical
  rw [Lax41Proofs.runCounts_eq_priorCount]
  unfold Lax41Proofs.priorCountFor
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma runCounts_eq_of_tablesAgreeThrough {n : ℕ}
    (H : SimpleGraph (Fin n)) {left right : SampleTable n} {B round : ℕ}
    (hagree : TablesAgreeThrough B left right) (hround : round ≤ B) :
    runCounts (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) (selectionRule H) left round =
      runCounts (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) (selectionRule H) right round := by
  classical
  induction round with
  | zero => rfl
  | succ round ih =>
      have hrB : round ≤ B := by omega
      rw [Lax41Proofs.runCounts_succ, Lax41Proofs.runCounts_succ,
        ih hrB]
      congr 1
      unfold resamplingLog
      rw [ih hrB]
      congr 1
      funext e
      apply hagree e
      exact (runCounts_le_round H right round e).trans hrB

lemma resamplingLog_eq_of_tablesAgreeThrough {n : ℕ}
    (H : SimpleGraph (Fin n)) {left right : SampleTable n} {B round : ℕ}
    (hagree : TablesAgreeThrough B left right) (hround : round ≤ B) :
    resamplingLog (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) (selectionRule H) left round =
      resamplingLog (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) (selectionRule H) right round := by
  classical
  unfold resamplingLog
  rw [runCounts_eq_of_tablesAgreeThrough H hagree hround]
  congr 1
  funext e
  apply hagree e
  exact (runCounts_le_round H right round e).trans hround

lemma cutoffAssignment_eq_of_tablesAgreeThrough {n : ℕ}
    (H : SimpleGraph (Fin n)) {left right : SampleTable n}
    (hagree : TablesAgreeThrough (cutoffBudget n) left right) :
    cutoffAssignment H left = cutoffAssignment H right := by
  classical
  unfold cutoffAssignment currentAssignment
  rw [runCounts_eq_of_tablesAgreeThrough H hagree (le_refl _)]
  funext e
  apply hagree e
  exact runCounts_le_round H right (cutoffBudget n) e

lemma haltedAtCutoff_iff_of_tablesAgreeThrough {n : ℕ}
    (H : SimpleGraph (Fin n)) {left right : SampleTable n}
    (hagree : TablesAgreeThrough (cutoffBudget n) left right) :
    haltedAtCutoff H left ↔ haltedAtCutoff H right := by
  unfold haltedAtCutoff
  rw [resamplingLog_eq_of_tablesAgreeThrough H hagree (le_refl _)]

lemma cutoffOutputGraph_eq_of_tablesAgreeThrough {n : ℕ}
    (H : SimpleGraph (Fin n)) {left right : SampleTable n}
    (hagree : TablesAgreeThrough (cutoffBudget n) left right) :
    cutoffOutputGraph H left = cutoffOutputGraph H right := by
  unfold cutoffOutputGraph
  rw [cutoffAssignment_eq_of_tablesAgreeThrough H hagree]

/-- The bounded output is determined by the finite prefix. -/
lemma truncatedGraph_eq_of_tablesAgreeThrough {n : ℕ}
    (H : SimpleGraph (Fin n)) {left right : SampleTable n}
    (hagree : TablesAgreeThrough (cutoffBudget n) left right) :
    truncatedGraph H left = truncatedGraph H right := by
  classical
  unfold truncatedGraph
  rw [show haltedAtCutoff H left = haltedAtCutoff H right by
    apply propext
    exact haltedAtCutoff_iff_of_tablesAgreeThrough H hagree]
  split_ifs
  · exact cutoffOutputGraph_eq_of_tablesAgreeThrough H hagree
  · rfl

/-- The finite prefix of Boolean edge samples. -/
abbrev FiniteTable (n : ℕ) :=
  (j : prefixIndices n) → Bool

/-- Extend a finite prefix by false cells that the bounded run never reads. -/
def extendFiniteTable {n : ℕ} (table : FiniteTable n) : SampleTable n :=
  fun j ↦ if h : j ∈ prefixIndices n then table ⟨j, h⟩ else false

@[simp] lemma extendFiniteTable_apply {n : ℕ} (table : FiniteTable n)
    (j : prefixIndices n) : extendFiniteTable table j = table j := by
  simp [extendFiniteTable, j.2]

lemma tablesAgreeThrough_extend_restrict {n : ℕ} (table : SampleTable n) :
    TablesAgreeThrough (cutoffBudget n)
      (extendFiniteTable ((prefixIndices n).restrict table)) table := by
  intro e r hr
  have hmem : (⟨e, r⟩ : TableIndex (Variable := EdgeVariable n)) ∈
      prefixIndices n := by
    simp
    omega
  simp [extendFiniteTable, hmem]

lemma truncatedGraph_extend_restrict {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) :
    truncatedGraph H (extendFiniteTable ((prefixIndices n).restrict table)) =
      truncatedGraph H table :=
  truncatedGraph_eq_of_tablesAgreeThrough H
    (tablesAgreeThrough_extend_restrict table)

/-- The finite Bernoulli product law on the cells read by the bounded run. -/
noncomputable def finiteTableMeasure (n : ℕ) :
    MeasureTheory.Measure (FiniteTable n) :=
  MeasureTheory.Measure.pi fun j : prefixIndices n ↦ distribution n j.1.1

/-- Every event about the bounded output has the same finite and infinite law. -/
lemma truncatedGraph_event_probability_finite {n : ℕ}
    (H : SimpleGraph (Fin n)) (P : SimpleGraph (BlowupVertex n) → Prop) :
    sampleMeasure n {table | P (truncatedGraph H table)} =
      finiteTableMeasure n
        {table | P (truncatedGraph H (extendFiniteTable table))} := by
  let target : Set (FiniteTable n) :=
    {table | P (truncatedGraph H (extendFiniteTable table))}
  have htarget : MeasurableSet target := Set.toFinite _ |>.measurableSet
  calc
    sampleMeasure n {table | P (truncatedGraph H table)} =
        sampleMeasure n ((prefixIndices n).restrict ⁻¹' target) := by
      congr 1
      ext table
      simp only [Set.mem_setOf_eq, Set.mem_preimage, target]
      rw [truncatedGraph_extend_restrict H table]
    _ = (MeasureTheory.Measure.map (prefixIndices n).restrict
          (sampleMeasure n)) target := by
      rw [MeasureTheory.Measure.map_apply (prefixIndices n).measurable_restrict
        htarget]
    _ = finiteTableMeasure n target := by
      unfold sampleMeasure tableMeasure finiteTableMeasure
      rw [MeasureTheory.Measure.infinitePi_map_restrict]

/-- Uniform probability measure on any nonempty finite type. -/
noncomputable def uniformMeasure (X : Type) [Fintype X] [Nonempty X]
    [MeasurableSpace X] : MeasureTheory.Measure X :=
  (PMF.uniformOfFintype X).toMeasure

lemma pi_uniformMeasure (I X : Type) [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] [MeasurableSpace X]
    [MeasurableSingletonClass X] :
    MeasureTheory.Measure.pi (fun _ : I ↦ uniformMeasure X) =
      uniformMeasure (I → X) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure (uniformMeasure X) := by
    unfold uniformMeasure
    infer_instance
  apply MeasureTheory.Measure.ext
  intro S hS
  let s : Finset (I → X) := S.toFinite.toFinset
  have hs : (s : Set (I → X)) = S := by
    simpa only [s] using S.toFinite.coe_toFinset
  rw [← hs]
  rw [← MeasureTheory.sum_measure_singleton,
    ← MeasureTheory.sum_measure_singleton]
  apply Finset.sum_congr rfl
  intro f hf
  have hsingleton : ({f} : Set (I → X)) =
      Set.pi Set.univ (fun i ↦ {f i}) := by
    ext g
    simp [funext_iff]
  have hmeasSingleton : MeasurableSet ({f} : Set (I → X)) := by
    rw [hsingleton]
    exact MeasurableSet.univ_pi fun i ↦ measurableSet_singleton (f i)
  conv_lhs => rw [hsingleton]
  rw [MeasureTheory.Measure.pi_pi]
  · unfold uniformMeasure
    rw [PMF.toMeasure_uniformOfFintype_apply {f} hmeasSingleton]
    simp_rw [PMF.toMeasure_apply_singleton (PMF.uniformOfFintype X) _
      (measurableSet_singleton _), PMF.uniformOfFintype_apply]
    rw [Fintype.card_fun, Nat.cast_pow]
    rw [Finset.prod_const, Finset.card_univ]
    simpa only [Fintype.card_unique, Nat.cast_one, one_div] using
      (ENNReal.inv_pow (a := (Fintype.card X : ℝ≥0∞))
        (n := Fintype.card I)).symm

/-- One edge sample is true exactly when every bit in its block is true. -/
def allTrue (k : ℕ) (block : Fin k → Bool) : Bool :=
  decide (∀ i, block i = true)

lemma map_uniform_allTrue_true (k : ℕ) :
    (PMF.uniformOfFintype (Fin k → Bool)).map (allTrue k) true =
      (((2 ^ k : ℕ) : ℝ≥0∞))⁻¹ := by
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  have hpred (a : Fin k → Bool) :
      (∀ i, a i = true) ↔ a = fun _ ↦ true := by
    constructor
    · intro h
      funext i
      exact h i
    · rintro rfl i
      rfl
  simp_rw [show ∀ a : Fin k → Bool,
    (true = allTrue k a) ↔ ∀ i, a i = true by
      intro a
      simp [allTrue]]
  simp_rw [hpred]
  simp

lemma map_uniform_allTrue (k : ℕ) :
    (PMF.uniformOfFintype (Fin k → Bool)).map (allTrue k) =
      PMF.bernoulli (((2 ^ k : ℕ) : NNReal)⁻¹) (by
        rw [inv_le_one₀]
        · exact_mod_cast Nat.one_le_two_pow
        · positivity) := by
  apply PMF.ext
  intro b
  cases b with
  | false =>
      have htotal := ((PMF.uniformOfFintype (Fin k → Bool)).map
        (allTrue k)).tsum_coe
      rw [tsum_bool, map_uniform_allTrue_true] at htotal
      simp only [PMF.bernoulli_apply, Bool.cond_false]
      rw [ENNReal.coe_sub, ENNReal.coe_one,
        ENNReal.coe_inv (by positivity : ((2 ^ k : ℕ) : NNReal) ≠ 0)]
      exact ENNReal.eq_sub_of_add_eq (by simp) htotal
  | true =>
      rw [PMF.bernoulli_apply]
      simp only [Bool.cond_true]
      rw [ENNReal.coe_inv (by positivity : ((2 ^ k : ℕ) : NNReal) ≠ 0)]
      exact map_uniform_allTrue_true k

/-- The uniform-bit block underlying one Bernoulli edge sample. -/
abbrev SampleBlock (n : ℕ) := Fin (sampleBits n) → Bool

/-- The actual finite family of independent uniform bits used by the reduction. -/
abbrev FiniteSeed (n : ℕ) :=
  (j : prefixIndices n) → SampleBlock n

/-- Decode uniform blocks to the finite Bernoulli table. -/
def seedFiniteTable {n : ℕ} (seed : FiniteSeed n) : FiniteTable n :=
  fun j ↦ allTrue (sampleBits n) (seed j)

/-- Uniform law on the finite bit family. -/
noncomputable def finiteSeedMeasure (n : ℕ) :
    MeasureTheory.Measure (FiniteSeed n) :=
  uniformMeasure (FiniteSeed n)

lemma map_uniformBlock_eq_distribution (n : ℕ) (e : EdgeVariable n) :
    MeasureTheory.Measure.map (allTrue (sampleBits n))
        (uniformMeasure (SampleBlock n)) = distribution n e := by
  unfold uniformMeasure distribution edgeChance edgeDenominator
  rw [PMF.toMeasure_map]
  · rw [map_uniform_allTrue]
  · fun_prop

/-- Decoding the finite uniform seed gives exactly the finite Bernoulli law. -/
lemma map_finiteSeedMeasure (n : ℕ) :
    MeasureTheory.Measure.map seedFiniteTable (finiteSeedMeasure n) =
      finiteTableMeasure n := by
  classical
  unfold finiteSeedMeasure finiteTableMeasure
  rw [← pi_uniformMeasure (prefixIndices n) (SampleBlock n)]
  unfold seedFiniteTable
  letI : MeasureTheory.IsProbabilityMeasure
      (uniformMeasure (SampleBlock n)) := by
    unfold uniformMeasure
    infer_instance
  letI : MeasureTheory.SigmaFinite
      (MeasureTheory.Measure.map (allTrue (sampleBits n))
        (uniformMeasure (SampleBlock n))) := by
    infer_instance
  rw [MeasureTheory.Measure.pi_map_pi]
  · congr 1
    funext j
    exact map_uniformBlock_eq_distribution n j.1.1
  · intro j
    fun_prop

lemma finiteSeed_event_probability (n : ℕ) (S : Set (FiniteTable n)) :
    finiteSeedMeasure n (seedFiniteTable ⁻¹' S) = finiteTableMeasure n S := by
  have hS : MeasurableSet S := Set.toFinite _ |>.measurableSet
  rw [← MeasureTheory.Measure.map_apply
    (by fun_prop : Measurable (@seedFiniteTable n)) hS]
  rw [map_finiteSeedMeasure]

/-- Number of independent fair bits supplied to the bounded reduction. -/
def finiteRandomBitCount (n : ℕ) : ℕ :=
  (prefixIndices n).card * sampleBits n

/-- The structured seed space contains exactly $2^r$ seeds for $r$ bits. -/
lemma card_finiteSeed (n : ℕ) :
    Fintype.card (FiniteSeed n) = 2 ^ finiteRandomBitCount n := by
  simp only [FiniteSeed, SampleBlock, Fintype.card_fun, Fintype.card_bool,
    finiteRandomBitCount, Fintype.card_coe, Fintype.card_fin]
  rw [← pow_mul]
  congr 1
  exact Nat.mul_comm _ _

lemma card_prefixIndices (n : ℕ) :
    (prefixIndices n).card =
      Fintype.card (EdgeVariable n) * (cutoffBudget n + 1) := by
  simp [prefixIndices]

lemma card_edgeVariable_le (n : ℕ) :
    Fintype.card (EdgeVariable n) ≤ n ^ 4 := by
  calc
    Fintype.card (EdgeVariable n) ≤
        Fintype.card (BlowupVertex n × BlowupVertex n) := by
      apply Fintype.card_le_of_surjective Sym2.mk.uncurry
      intro edge
      induction edge using Sym2.inductionOn with
      | _ left right => exact ⟨(left, right), rfl⟩
    _ = n ^ 4 := by simp [BlowupVertex]; ring

lemma sampleBits_le_linear (n : ℕ) : sampleBits n ≤ 101 * (n + 1) := by
  unfold sampleBits
  calc
    Nat.log2 (100 * (n + 1)) + 1 ≤ 100 * (n + 1) + 1 := by
      gcongr
      exact Nat.log2_le_self _
    _ ≤ 101 * (n + 1) := by omega

/-- The number of random bits is bounded by an explicit polynomial. -/
lemma finiteRandomBitCount_polynomial (n : ℕ) :
    finiteRandomBitCount n ≤ 1400 * (n + 1) ^ 12 := by
  rw [finiteRandomBitCount, card_prefixIndices]
  have hedge : Fintype.card (EdgeVariable n) ≤ (n + 1) ^ 4 :=
    (card_edgeVariable_le n).trans (by gcongr; omega)
  have hbudget : cutoffBudget n + 1 ≤ 13 * (n + 1) ^ 6 := by
    simp only [cutoffBudget]
    have hbase : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have hbits := sampleBits_le_linear n
  calc
    Fintype.card (EdgeVariable n) * (cutoffBudget n + 1) * sampleBits n ≤
        (n + 1) ^ 4 * (13 * (n + 1) ^ 6) * (101 * (n + 1)) := by
      gcongr
    _ ≤ 1400 * (n + 1) ^ 12 := by
      have hbase : 1 ≤ n + 1 := by omega
      calc
        (n + 1) ^ 4 * (13 * (n + 1) ^ 6) * (101 * (n + 1)) =
            1313 * (n + 1) ^ 11 := by ring
        _ ≤ 1400 * (n + 1) ^ 12 := by
          nlinarith [pow_le_pow_right₀ hbase (by omega : 11 ≤ 12)]

lemma three_mul_le_of_ratio_le_third (a b : ℕ) (hb : 0 < b)
    (h : (a : ℝ≥0∞) / b ≤ (1 : ℝ≥0∞) / 3) : 3 * a ≤ b := by
  have ha : (a : ℝ≥0∞) ≤ (1 / 3 : ℝ≥0∞) * b :=
    (ENNReal.div_le_iff (by exact_mod_cast Nat.ne_of_gt hb)
      (ENNReal.natCast_ne_top b)).mp h
  have hcross : (a : ℝ≥0∞) ≤ b / 3 := by
    calc
      (a : ℝ≥0∞) ≤ (1 / 3 : ℝ≥0∞) * b := ha
      _ = b / 3 := by simp only [div_eq_mul_inv, one_mul, mul_comm]
  have hmul : (a : ℝ≥0∞) * 3 ≤ b :=
    (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))).mp hcross
  have hnat : a * 3 ≤ b := by exact_mod_cast hmul
  simpa [mul_comm] using hnat

/-- A measure bound on a finite uniform bit space is the required count bound. -/
lemma filter_card_le_third_of_measure_le (n : ℕ)
    (P : FiniteSeed n → Prop) [DecidablePred P]
    (hmeasure : finiteSeedMeasure n {seed | P seed} ≤ (1 : ℝ≥0∞) / 3) :
    3 * (Finset.univ.filter P).card ≤
      (Finset.univ : Finset (FiniteSeed n)).card := by
  classical
  have hmeas : MeasurableSet ({seed | P seed} : Set (FiniteSeed n)) :=
    Set.toFinite _ |>.measurableSet
  have hratio :
      ((Finset.univ.filter P).card : ℝ≥0∞) /
          (Finset.univ : Finset (FiniteSeed n)).card ≤ (1 : ℝ≥0∞) / 3 := by
    unfold finiteSeedMeasure uniformMeasure at hmeasure
    rw [PMF.toMeasure_uniformOfFintype_apply {seed | P seed} hmeas] at hmeasure
    simpa only [Fintype.card_subtype, Finset.setOf_mem, Finset.card_univ] using hmeasure
  apply three_mul_le_of_ratio_le_third _ _
  · simp
  · exact hratio

/-- The infinite-product soundness theorem transferred to finite uniform bits. -/
theorem finiteSeed_truncatedGraph_soundness_failure_le_third
    (n : ℕ) (hn : 3 ≤ n) (H : SimpleGraph (Fin n)) :
    finiteSeedMeasure n
      {seed | 40000 * H.indepNum * n * Real.log n <
        ((truncatedGraph H
          (extendFiniteTable (seedFiniteTable seed))).indepNum : ℝ)} ≤
      (1 : ℝ≥0∞) / 3 := by
  let P : SimpleGraph (BlowupVertex n) → Prop := fun graph ↦
    40000 * H.indepNum * n * Real.log n < (graph.indepNum : ℝ)
  let target : Set (FiniteTable n) := fun table ↦
    P (truncatedGraph H (extendFiniteTable table))
  calc
    finiteSeedMeasure n
        {seed | 40000 * H.indepNum * n * Real.log n <
          ((truncatedGraph H
            (extendFiniteTable (seedFiniteTable seed))).indepNum : ℝ)} =
        finiteTableMeasure n target := by
      simpa only [P, target, Set.preimage_setOf_eq] using
        finiteSeed_event_probability n target
    _ = sampleMeasure n {table | P (truncatedGraph H table)} :=
      (truncatedGraph_event_probability_finite H P).symm
    _ ≤ (1 : ℝ≥0∞) / 3 := by
      simpa only [P] using truncatedGraph_soundness_failure_le_third n hn H

end Lax47Proofs.FiniteExecution
