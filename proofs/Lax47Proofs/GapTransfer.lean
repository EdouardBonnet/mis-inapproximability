import Lax47Proofs.Construction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace Lax47Proofs.GapTransfer

open scoped ENNReal
open Lax47.Complexity Lax47.Reduction
open Filter Asymptotics

lemma rpow_square (n : ℕ) (a : ℝ) :
    Real.rpow (n * n) a = Real.rpow n (2 * a) := by
  rw [← pow_two]
  rw [← Real.rpow_natCast]
  exact (Real.rpow_mul (by positivity) 2 a).symm

/-- The acceptance threshold $n^{1+3\delta}$ from the paper. -/
noncomputable def gapThreshold (δ : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (1 + 3 * δ)

/-- A high-gap input is accepted for every sample table. -/
lemma high_output_card (R : TriangleFreeReduction)
    {ε δ : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    (hδε : 2 * δ ≤ ε) (n : ℕ) (hn : 1 ≤ n)
    (H : SimpleGraph (Fin n)) (table : SampleTable n)
    (hhigh : Real.rpow n (1 - δ) ≤ (H.indepNum : ℝ)) :
    gapThreshold δ n ≤
      (algorithm.output (BlowupVertex n) (R.output n H table)).card := by
  let G := R.output n H table
  let S := algorithm.output (BlowupVertex n) G
  let factor := Real.rpow (n * n) ((1 : ℝ) / 2 - ε)
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor : factor = Real.rpow n (1 - 2 * ε) := by
    dsimp only [factor]
    calc
      Real.rpow (n * n) ((1 : ℝ) / 2 - ε) =
          Real.rpow n (2 * ((1 : ℝ) / 2 - ε)) := rpow_square n _
      _ = Real.rpow n (1 - 2 * ε) := by congr 1 <;> ring
  have hfactorPos : 0 < factor := by
    dsimp only [factor]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hExponent : (1 - 2 * ε) + (1 + 3 * δ) ≤ 2 - δ := by
    nlinarith
  have hPower : factor * gapThreshold δ n ≤ Real.rpow n (2 - δ) := by
    rw [hfactor, gapThreshold]
    change (n : ℝ) ^ (1 - 2 * ε) * (n : ℝ) ^ (1 + 3 * δ) ≤
      (n : ℝ) ^ (2 - δ)
    rw [← Real.rpow_add hnpos]
    exact Real.rpow_le_rpow_of_exponent_le hnOne hExponent
  have hHighPower : Real.rpow n (2 - δ) ≤ (H.indepNum : ℝ) * n := by
    calc
      Real.rpow n (2 - δ) = Real.rpow n ((1 - δ) + 1) := by congr 1 <;> ring
      _ = Real.rpow n (1 - δ) * Real.rpow n 1 := Real.rpow_add hnpos _ _
      _ = Real.rpow n (1 - δ) * n := by
        rw [Real.rpow_eq_pow n (1 - δ), Real.rpow_eq_pow n 1, Real.rpow_one]
      _ ≤ (H.indepNum : ℝ) * n :=
        mul_le_mul_of_nonneg_right hhigh (by positivity)
  have hComplete : (H.indepNum : ℝ) * n ≤ (G.indepNum : ℝ) := by
    exact_mod_cast R.completeness n H table
  have hApproximation : (G.indepNum : ℝ) ≤ factor * S.card := by
    have h := algorithm.approximation (BlowupVertex n) G (R.triangleFree n H table)
    simpa only [BlowupVertex, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_mul, G, S, factor] using h
  have hProduct : factor * gapThreshold δ n ≤ factor * S.card :=
    hPower.trans (hHighPower.trans (hComplete.trans hApproximation))
  exact le_of_mul_le_mul_left hProduct hfactorPos

/-- Eventually $C\log n<n^{2\delta}$. -/
lemma exists_log_cutoff (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      C * Real.log n < Real.rpow n (2 * δ) := by
  have hsmall : (fun x : ℝ => C * Real.log x) =o[atTop]
      (fun x : ℝ => Real.rpow x (2 * δ)) :=
    (isLittleO_log_rpow_atTop (by positivity)).const_mul_left C
  have hnat := hsmall.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hnat.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  rcases Filter.eventually_atTop.1 hbound with ⟨n₁, hn₁⟩
  refine ⟨max n₁ 3, ?_⟩
  intro n hn
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have h := hn₁ n hn1
  simp only [Function.comp_apply] at h
  have hlog : 0 ≤ C * Real.log n := by
    have : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn3))
    positivity
  have hrpow : 0 < Real.rpow n (2 * δ) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hn3)
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos hrpow] at h
  nlinarith

/-- A low-gap input can be accepted only on a reduction soundness failure. -/
lemma low_soundness_threshold (C δ : ℝ) (hC : 0 < C)
    (n : ℕ) (hn : 3 ≤ n) (H : SimpleGraph (Fin n))
    (hlow : (H.indepNum : ℝ) ≤ Real.rpow n δ)
    (hlog : C * Real.log n < Real.rpow n (2 * δ)) :
    C * H.indepNum * n * Real.log n < gapThreshold δ n := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hn)
  have hαn : (H.indepNum : ℝ) * n ≤ Real.rpow n (1 + δ) := by
    calc
      (H.indepNum : ℝ) * n ≤ Real.rpow n δ * n :=
        mul_le_mul_of_nonneg_right hlow (by positivity)
      _ = Real.rpow n δ * Real.rpow n 1 := by
        rw [Real.rpow_eq_pow n 1, Real.rpow_one]
      _ = Real.rpow n (δ + 1) := (Real.rpow_add hnpos δ 1).symm
      _ = Real.rpow n (1 + δ) := by congr 1 <;> ring
  have hCLog : 0 ≤ C * Real.log n := by
    have : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn))
    positivity
  have hPowerPos : 0 < Real.rpow n (1 + δ) :=
    Real.rpow_pos_of_pos hnpos _
  calc
    C * H.indepNum * n * Real.log n =
        (C * Real.log n) * ((H.indepNum : ℝ) * n) := by ring
    _ ≤ (C * Real.log n) * Real.rpow n (1 + δ) :=
      mul_le_mul_of_nonneg_left hαn hCLog
    _ < Real.rpow n (2 * δ) * Real.rpow n (1 + δ) :=
      mul_lt_mul_of_pos_right hlog hPowerPos
    _ = Real.rpow n ((2 * δ) + (1 + δ)) :=
      (Real.rpow_add hnpos (2 * δ) (1 + δ)).symm
    _ = gapThreshold δ n := by
      rw [gapThreshold]
      congr 1 <;> ring

/-- Reduction work plus approximation-algorithm work. -/
noncomputable def gapSteps (R : TriangleFreeReduction)
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    (n : ℕ) (H : SimpleGraph (Fin n)) (table : SampleTable n) : ℕ :=
  R.steps n H table + algorithm.steps (BlowupVertex n) (R.output n H table)

lemma gapSteps_polynomial (R : TriangleFreeReduction)
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    (n : ℕ) (H : SimpleGraph (Fin n)) (table : SampleTable n) :
    gapSteps R algorithm n H table ≤
      polynomialBound (R.stepConstant + algorithm.stepConstant)
        (max R.stepExponent (2 * algorithm.stepExponent)) n := by
  let k : ℕ := max R.stepExponent (2 * algorithm.stepExponent)
  have hAlgorithm := algorithm.stepBound (BlowupVertex n) (R.output n H table)
  simp only [BlowupVertex, Fintype.card_prod, Fintype.card_fin,
    polynomialBound] at hAlgorithm
  have hsquare : n * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hAlgorithmPower : (n * n + 1) ^ algorithm.stepExponent ≤
      (n + 1) ^ (2 * algorithm.stepExponent) := by
    calc
      (n * n + 1) ^ algorithm.stepExponent ≤
          ((n + 1) ^ 2) ^ algorithm.stepExponent :=
        pow_le_pow_left' hsquare _
      _ = (n + 1) ^ (2 * algorithm.stepExponent) := by rw [pow_mul]
  have hbase : 1 ≤ n + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have hRPower : (n + 1) ^ R.stepExponent ≤ (n + 1) ^ k :=
    pow_le_pow_right' hbase (le_max_left _ _)
  have hAlgorithmPower' : (n + 1) ^ (2 * algorithm.stepExponent) ≤
      (n + 1) ^ k :=
    pow_le_pow_right' hbase (le_max_right _ _)
  have hR' : R.steps n H table ≤ R.stepConstant * (n + 1) ^ k :=
    (R.stepBound n H table).trans (Nat.mul_le_mul_left R.stepConstant hRPower)
  have hAlgorithm' : algorithm.steps (BlowupVertex n) (R.output n H table) ≤
      algorithm.stepConstant * (n + 1) ^ k :=
    hAlgorithm.trans (Nat.mul_le_mul_left algorithm.stepConstant
      (hAlgorithmPower.trans hAlgorithmPower'))
  calc
    gapSteps R algorithm n H table =
        R.steps n H table + algorithm.steps (BlowupVertex n) (R.output n H table) := rfl
    _ ≤ R.stepConstant * (n + 1) ^ k + algorithm.stepConstant * (n + 1) ^ k :=
      Nat.add_le_add hR' hAlgorithm'
    _ = polynomialBound (R.stepConstant + algorithm.stepConstant) k n := by
      simp only [polynomialBound]
      ring

noncomputable def reductionProbabilitySpace (R : TriangleFreeReduction)
    (n : ℕ) : ProbabilitySpace where
  Sample := SampleTable n
  measurableSpace := inferInstance
  measure := R.measure n
  probability := R.probability n

/-- Accept when the returned independent set reaches $n^{1+3\delta}$. -/
noncomputable def gapAccepts (R : TriangleFreeReduction)
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε) (δ : ℝ)
    (n : ℕ) (H : SimpleGraph (Fin n)) (table : SampleTable n) : Prop :=
  gapThreshold δ n ≤
    (algorithm.output (BlowupVertex n) (R.output n H table)).card

/-- The reduction and a triangle-free approximation give a general MIS gap solver. -/
noncomputable def gapSolver (R : TriangleFreeReduction)
    {ε δ : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    (hδ : 0 < δ) (hδε : 2 * δ ≤ ε) : MISGapSolver δ := by
  classical
  let C := R.soundnessConstant
  let nR := R.soundnessCutoff
  let nLog : ℕ := Classical.choose
    (exists_log_cutoff C δ R.soundnessConstant_pos hδ)
  have hLog : ∀ n : ℕ, nLog ≤ n →
      C * Real.log n < Real.rpow n (2 * δ) :=
    Classical.choose_spec (exists_log_cutoff C δ R.soundnessConstant_pos hδ)
  let c := R.stepConstant + algorithm.stepConstant
  let k := max R.stepExponent (2 * algorithm.stepExponent)
  let cutoff := max (max nR nLog) 3
  refine
    { sampleSpace := reductionProbabilitySpace R
      accepts := gapAccepts R algorithm δ
      steps := gapSteps R algorithm
      stepConstant := c
      stepExponent := k
      stepConstant_pos := Nat.add_pos_left R.stepConstant_pos _
      stepBound := gapSteps_polynomial R algorithm
      cutoff := cutoff
      completeness := ?_
      soundness := ?_ }
  · intro n hn H hhigh
    have hnLog : nLog ≤ n :=
      (le_max_right nR nLog).trans ((le_max_left (max nR nLog) 3).trans hn)
    have hn3 : 3 ≤ n := (le_max_right (max nR nLog) 3).trans hn
    have hall : {table : SampleTable n | gapAccepts R algorithm δ n H table} =
        Set.univ := by
      ext table
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact high_output_card R algorithm hδε n (by omega) H table hhigh
    change (2 : ℝ≥0∞) / 3 ≤ R.measure n
      {table : SampleTable n | gapAccepts R algorithm δ n H table}
    rw [hall]
    letI : MeasureTheory.IsProbabilityMeasure (R.measure n) := R.probability n
    simp
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num
  · intro n hn H hlow
    have hnPair : max nR nLog ≤ n :=
      (le_max_left (max nR nLog) 3).trans hn
    have hnR : nR ≤ n := (le_max_left nR nLog).trans hnPair
    have hnLog : nLog ≤ n := (le_max_right nR nLog).trans hnPair
    have hn3 : 3 ≤ n := (le_max_right (max nR nLog) 3).trans hn
    have hsubset :
        {table : SampleTable n | gapAccepts R algorithm δ n H table} ⊆
        {table | C * H.indepNum * n * Real.log n <
          ((R.output n H table).indepNum : ℝ)} := by
      intro table haccept
      have hthreshold := low_soundness_threshold C δ
        R.soundnessConstant_pos n hn3 H hlow (hLog n hnLog)
      have hindependent := algorithm.independent (BlowupVertex n)
        (R.output n H table) (R.triangleFree n H table)
      have hcard : (algorithm.output (BlowupVertex n)
          (R.output n H table)).card ≤ (R.output n H table).indepNum :=
        hindependent.card_le_indepNum
      exact hthreshold.trans_le (haccept.trans (by exact_mod_cast hcard))
    change R.measure n {table : SampleTable n | gapAccepts R algorithm δ n H table} ≤
      (1 : ℝ≥0∞) / 3
    exact (MeasureTheory.measure_mono hsubset).trans (R.soundness n hnR H)

/-- A choice satisfying $0<\delta<1/2$ and $2\delta\leq\varepsilon$. -/
noncomputable def chosenDelta (ε : ℝ) : ℝ :=
  min (ε / 2) (1 / 4)

lemma chosenDelta_pos {ε : ℝ} (hε : 0 < ε) : 0 < chosenDelta ε := by
  rw [chosenDelta]
  exact lt_min (by positivity) (by norm_num)

lemma chosenDelta_lt_half (ε : ℝ) : chosenDelta ε < (1 : ℝ) / 2 := by
  calc
    chosenDelta ε ≤ (1 : ℝ) / 4 := min_le_right _ _
    _ < (1 : ℝ) / 2 := by norm_num

lemma two_mul_chosenDelta_le {ε : ℝ} : 2 * chosenDelta ε ≤ ε := by
  have h := min_le_left (ε / 2) ((1 : ℝ) / 4)
  rw [← chosenDelta] at h
  linarith

end Lax47Proofs.GapTransfer
