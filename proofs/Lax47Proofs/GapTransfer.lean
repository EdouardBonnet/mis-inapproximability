import Lax47.Hastad
import Lax47Proofs.OperationalReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace Lax47Proofs.GapTransfer

open Lax47.Machine Lax47.Complexity Lax47.Reduction Lax47.Gap
open Lax47Proofs.Construction Lax47Proofs.FiniteExecution
open Lax47Proofs.OperationalReduction
open Filter Asymptotics

/-! ### Correctness and cost of the executable threshold arithmetic -/

lemma countedMul_value (left right : ℕ) :
    (countedMul left right).1 = left * right := by
  induction right with
  | zero => simp [countedMul]
  | succ right ih =>
      simp [countedMul, ih, Nat.mul_succ]

lemma countedMul_steps (left right : ℕ) :
    (countedMul left right).2 = 1 + right * (left + 1) := by
  induction right with
  | zero => simp [countedMul]
  | succ right ih =>
      simp [countedMul, ih]
      ring

lemma countedPow_value (base exponent : ℕ) :
    (countedPow base exponent).1 = base ^ exponent := by
  induction exponent with
  | zero => simp [countedPow]
  | succ exponent ih =>
      simp [countedPow, countedMul_value, ih, Nat.pow_succ]

lemma countedPow_steps_le (base exponent : ℕ) :
    (countedPow base exponent).2 ≤
      4 * (exponent + 1) * (base + 2) ^ (exponent + 2) := by
  induction exponent with
  | zero =>
      simp only [countedPow]
      have hone : 1 ≤ (base + 2) ^ 2 :=
        Nat.one_le_pow _ _ (by omega)
      exact (show 1 ≤ 4 * 1 by norm_num).trans
        (Nat.mul_le_mul_left 4 hone)
  | succ exponent ih =>
      rw [countedPow]
      simp only [countedMul_steps, countedPow_value]
      let x := base + 2
      have hx : 1 ≤ x := by omega
      have hbase : base ≤ x := by omega
      have hproduct : base * base ^ exponent ≤ x ^ (exponent + 2) := by
        calc
          base * base ^ exponent = base ^ (exponent + 1) := by
            rw [Nat.pow_succ]
            ac_rfl
          _ ≤ x ^ (exponent + 1) := pow_le_pow_left' hbase _
          _ ≤ x ^ (exponent + 2) :=
            pow_le_pow_right' hx (by omega : exponent + 1 ≤ exponent + 2)
      have hbaseGrow : base ≤ x ^ (exponent + 2) := by
        calc
          base ≤ x := hbase
          _ = x ^ 1 := by simp
          _ ≤ x ^ (exponent + 2) :=
            pow_le_pow_right' hx (by omega : 1 ≤ exponent + 2)
      have hone : 1 ≤ x ^ (exponent + 2) := Nat.one_le_pow _ _ hx
      have hgrow : x ^ (exponent + 2) ≤ x ^ (exponent + 3) :=
        pow_le_pow_right' hx (by omega : exponent + 2 ≤ exponent + 3)
      have ih' : (countedPow base exponent).2 ≤
          4 * (exponent + 1) * x ^ (exponent + 2) := by
        simpa only [x] using ih
      calc
        (countedPow base exponent).2 +
              (1 + base * (base ^ exponent + 1)) + 1 ≤
            4 * (exponent + 1) * x ^ (exponent + 2) +
              (1 + (x ^ (exponent + 2) + x ^ (exponent + 2))) + 1 := by
          have hmul : base * (base ^ exponent + 1) ≤
              x ^ (exponent + 2) + x ^ (exponent + 2) := by
            rw [Nat.mul_add]
            simpa only [Nat.mul_one] using Nat.add_le_add hproduct hbaseGrow
          exact Nat.add_le_add_right
            (Nat.add_le_add ih' (Nat.add_le_add_left hmul 1)) 1
        _ ≤ 4 * (exponent + 1) * x ^ (exponent + 3) +
              (1 + (x ^ (exponent + 3) + x ^ (exponent + 3))) + 1 := by
          gcongr
        _ ≤ 4 * (exponent + 2) * x ^ (exponent + 3) := by
          have hone' : 1 ≤ x ^ (exponent + 3) := hone.trans hgrow
          nlinarith
        _ = 4 * (Nat.succ exponent + 1) *
              x ^ (Nat.succ exponent + 2) := by
          simp only [Nat.succ_eq_add_one]

lemma gapDecision_value (q n outputCard : ℕ) :
    (gapDecision q n outputCard).1 = true ↔
      n ^ (q + 3) ≤ outputCard ^ q := by
  simp [gapDecision, countedPow_value]

lemma gapDecision_steps_le (q n outputCard : ℕ) :
    (gapDecision q n outputCard).2 ≤
      10 * (q + 4) * (n + outputCard + 2) ^ (q + 5) := by
  let x := n + outputCard + 2
  have hx : 1 ≤ x := by omega
  have hn : n + 2 ≤ x := by omega
  have hk : outputCard + 2 ≤ x := by omega
  have hleft := countedPow_steps_le n (q + 3)
  have hright := countedPow_steps_le outputCard q
  have hleft' : (countedPow n (q + 3)).2 ≤
      4 * (q + 4) * x ^ (q + 5) := by
    simpa only [show q + 3 + 1 = q + 4 by omega,
      show q + 3 + 2 = q + 5 by omega] using
      hleft.trans (Nat.mul_le_mul_left (4 * (q + 4))
        (pow_le_pow_left' hn (q + 5)))
  have hright' : (countedPow outputCard q).2 ≤
      4 * (q + 4) * x ^ (q + 5) := by
    calc
      (countedPow outputCard q).2 ≤
          4 * (q + 1) * (outputCard + 2) ^ (q + 2) := hright
      _ ≤ 4 * (q + 4) * x ^ (q + 5) := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 4 (by omega : q + 1 ≤ q + 4))
          ((pow_le_pow_left' hk (q + 2)).trans
            (pow_le_pow_right' hx (by omega : q + 2 ≤ q + 5)))
  have hnvalue : n ^ (q + 3) ≤ x ^ (q + 5) :=
    (pow_le_pow_left' (by omega : n ≤ x) _).trans
      (pow_le_pow_right' hx (by omega : q + 3 ≤ q + 5))
  have hkvalue : outputCard ^ q ≤ x ^ (q + 5) :=
    (pow_le_pow_left' (by omega : outputCard ≤ x) _).trans
      (pow_le_pow_right' hx (by omega : q ≤ q + 5))
  simp only [gapDecision, countedPow_value]
  have hone : 1 ≤ x ^ (q + 5) := Nat.one_le_pow _ _ hx
  calc
    (countedPow n (q + 3)).2 + (countedPow outputCard q).2 +
          n ^ (q + 3) + outputCard ^ q + 1 ≤
        4 * (q + 4) * x ^ (q + 5) +
          4 * (q + 4) * x ^ (q + 5) +
          x ^ (q + 5) + x ^ (q + 5) + 1 := by omega
    _ ≤ 10 * (q + 4) * x ^ (q + 5) := by nlinarith

/-! ### Uniform executable seeds -/

lemma card_executionSeed (n : ℕ) :
    Fintype.card (ExecutionSeed n) = 2 ^ finiteRandomBitCount n := by
  exact (Fintype.card_congr (finiteSeedEquivExecution n)).symm.trans
    (card_finiteSeed n)

lemma filter_card_equiv {A B : Type} [Fintype A] [Fintype B]
    (equiv : A ≃ B) (predicate : B → Prop) [DecidablePred predicate] :
    ((Finset.univ : Finset A).filter fun value ↦ predicate (equiv value)).card =
      ((Finset.univ : Finset B).filter predicate).card := by
  classical
  have hcard := Fintype.card_congr
    (equiv.subtypeEquiv (p := fun value ↦ predicate (equiv value))
      (q := predicate) (fun _ ↦ Iff.rfl))
  simpa only [Fintype.card_subtype, Finset.setOf_mem, Finset.card_univ] using hcard

theorem executionSeed_soundness_failure_card_le_third
    (n : ℕ) (hn : 3 ≤ n) (input : GraphCode n) :
    3 * ((Finset.univ : Finset (ExecutionSeed n)).filter fun seed ↦
      40000 * input.graph.indepNum * n * Real.log n <
        ((executionOutput input seed).graph.indepNum : ℝ)).card ≤
      (Finset.univ : Finset (ExecutionSeed n)).card := by
  classical
  have hfinite := executionOutput_soundness_failure_card_le_third n hn input
  have hbad := filter_card_equiv (finiteSeedEquivExecution n)
    (fun seed : ExecutionSeed n ↦
      40000 * input.graph.indepNum * n * Real.log n <
        ((executionOutput input seed).graph.indepNum : ℝ))
  have htotal := Fintype.card_congr (finiteSeedEquivExecution n)
  have hbad' :
      ((Finset.univ : Finset (FiniteSeed n)).filter fun seed ↦
        40000 * input.graph.indepNum * n * Real.log n <
          ((executionOutput input
            (executionSeedOfFinite seed)).graph.indepNum : ℝ)).card =
      ((Finset.univ : Finset (ExecutionSeed n)).filter fun seed ↦
        40000 * input.graph.indepNum * n * Real.log n <
          ((executionOutput input seed).graph.indepNum : ℝ)).card := by
    simpa only [finiteSeedEquivExecution] using hbad
  rw [hbad'] at hfinite
  exact hfinite.trans_eq (by
    simpa only [Finset.card_univ] using htotal)

/-! ### The real gap arithmetic -/

lemma rpow_square (n : ℕ) (a : ℝ) :
    Real.rpow (n * n) a = Real.rpow n (2 * a) := by
  rw [← pow_two]
  rw [← Real.rpow_natCast]
  exact (Real.rpow_mul (by positivity) 2 a).symm

/-- The paper's real acceptance threshold $n^{1+3/q}$. -/
noncomputable def realGapThreshold (q n : ℕ) : ℝ :=
  Real.rpow n (1 + 3 * (q : ℝ)⁻¹)

lemma naturalGapThreshold_iff {q : ℕ} (hq : 0 < q) (n outputCard : ℕ) :
    n ^ (q + 3) ≤ outputCard ^ q ↔
      realGapThreshold q n ≤ outputCard := by
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hqNe : (q : ℝ) ≠ 0 := hqReal.ne'
  have hexponent : (1 + 3 * (q : ℝ)⁻¹) * (q : ℝ) = (q : ℝ) + 3 := by
    field_simp [hqNe]
  have hcastExponent : (q : ℝ) + 3 = ((q + 3 : ℕ) : ℝ) := by
    norm_num
  have hthreshold : Real.rpow (realGapThreshold q n) (q : ℝ) =
      ((n ^ (q + 3) : ℕ) : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [realGapThreshold, Real.rpow_eq_pow,
      ← Real.rpow_mul (by positivity), hexponent, hcastExponent,
      Real.rpow_natCast]
    norm_cast
  have houtput : Real.rpow (outputCard : ℝ) (q : ℝ) =
      ((outputCard ^ q : ℕ) : ℝ) := by
    simp only [Real.rpow_eq_pow, Real.rpow_natCast]
    norm_cast
  have hthresholdNonneg : 0 ≤ realGapThreshold q n := by
    simpa only [realGapThreshold, Real.rpow_eq_pow] using
      Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity)
        (1 + 3 * (q : ℝ)⁻¹)
  have hiff :
      Real.rpow (realGapThreshold q n) (q : ℝ) ≤
          Real.rpow (outputCard : ℝ) (q : ℝ) ↔
        realGapThreshold q n ≤ outputCard := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_rpow_iff hthresholdNonneg
        (by positivity : (0 : ℝ) ≤ outputCard) hqReal
  constructor
  · intro h
    have hcast : ((n ^ (q + 3) : ℕ) : ℝ) ≤
        ((outputCard ^ q : ℕ) : ℝ) := by exact_mod_cast h
    apply hiff.mp
    simpa only [hthreshold, houtput] using hcast
  · intro h
    have hrpow := hiff.mpr h
    rw [hthreshold, houtput] at hrpow
    exact_mod_cast hrpow

lemma high_output_card {q : ℕ} {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε)
    (hqε : 2 * (q : ℝ)⁻¹ ≤ ε) (n : ℕ) (hn : 1 ≤ n)
    (input : GraphCode n) (seed : ExecutionSeed n)
    (hhigh : Real.rpow n (1 - (q : ℝ)⁻¹) ≤
      (input.graph.indepNum : ℝ)) :
    realGapThreshold q n ≤
      (algorithm.output (executionOutput input seed)).card := by
  let graph := executionOutput input seed
  let set := algorithm.output graph
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
  have hExponent :
      (1 - 2 * ε) + (1 + 3 * (q : ℝ)⁻¹) ≤
        2 - (q : ℝ)⁻¹ := by
    nlinarith
  have hPower : factor * realGapThreshold q n ≤
      Real.rpow n (2 - (q : ℝ)⁻¹) := by
    rw [hfactor, realGapThreshold]
    calc
      Real.rpow n (1 - 2 * ε) *
          Real.rpow n (1 + 3 * (q : ℝ)⁻¹) =
          Real.rpow n ((1 - 2 * ε) + (1 + 3 * (q : ℝ)⁻¹)) := by
            simpa only [Real.rpow_eq_pow] using
              (Real.rpow_add hnpos (1 - 2 * ε)
                (1 + 3 * (q : ℝ)⁻¹)).symm
      _ ≤ Real.rpow n (2 - (q : ℝ)⁻¹) := by
        simpa only [Real.rpow_eq_pow] using
          Real.rpow_le_rpow_of_exponent_le hnOne hExponent
  have hHighPower : Real.rpow n (2 - (q : ℝ)⁻¹) ≤
      (input.graph.indepNum : ℝ) * n := by
    calc
      Real.rpow n (2 - (q : ℝ)⁻¹) =
          Real.rpow n ((1 - (q : ℝ)⁻¹) + 1) := by congr 1 <;> ring
      _ = Real.rpow n (1 - (q : ℝ)⁻¹) * Real.rpow n 1 :=
        by simpa only [Real.rpow_eq_pow] using Real.rpow_add hnpos _ _
      _ = Real.rpow n (1 - (q : ℝ)⁻¹) * n := by
        simp only [Real.rpow_eq_pow, Real.rpow_one]
      _ ≤ (input.graph.indepNum : ℝ) * n :=
        mul_le_mul_of_nonneg_right hhigh (by positivity)
  have hComplete : (input.graph.indepNum : ℝ) * n ≤
      (graph.graph.indepNum : ℝ) := by
    exact_mod_cast executionOutput_completeness_of_executionSeed input seed
  have hApproximation : (graph.graph.indepNum : ℝ) ≤ factor * set.card := by
    simpa only [graph, set, factor, Nat.cast_mul] using
      algorithm.approximation graph
        (executionOutput_triangleFree_of_executionSeed input seed)
  have hProduct : factor * realGapThreshold q n ≤ factor * set.card :=
    hPower.trans (hHighPower.trans (hComplete.trans hApproximation))
  exact le_of_mul_le_mul_left hProduct hfactorPos

/-- Eventually $C\log n<n^{2/q}$. -/
lemma exists_log_cutoff (C : ℝ) (q : ℕ) (hC : 0 < C) (hq : 0 < q) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      C * Real.log n < Real.rpow n (2 * (q : ℝ)⁻¹) := by
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hexponent : 0 < 2 * (q : ℝ)⁻¹ := by positivity
  have hsmall : (fun x : ℝ => C * Real.log x) =o[atTop]
      (fun x : ℝ => Real.rpow x (2 * (q : ℝ)⁻¹)) :=
    (isLittleO_log_rpow_atTop hexponent).const_mul_left C
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
  have hrpow : 0 < Real.rpow n (2 * (q : ℝ)⁻¹) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hn3)
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos hrpow] at h
  nlinarith

lemma low_soundness_threshold (C : ℝ) (q n : ℕ) (hC : 0 < C)
    (hn : 3 ≤ n) (input : GraphCode n)
    (hlow : (input.graph.indepNum : ℝ) ≤ Real.rpow n (q : ℝ)⁻¹)
    (hlog : C * Real.log n < Real.rpow n (2 * (q : ℝ)⁻¹)) :
    C * input.graph.indepNum * n * Real.log n < realGapThreshold q n := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hn)
  have hαn : (input.graph.indepNum : ℝ) * n ≤
      Real.rpow n (1 + (q : ℝ)⁻¹) := by
    calc
      (input.graph.indepNum : ℝ) * n ≤ Real.rpow n (q : ℝ)⁻¹ * n :=
        mul_le_mul_of_nonneg_right hlow (by positivity)
      _ = Real.rpow n (q : ℝ)⁻¹ * Real.rpow n 1 := by
        simp only [Real.rpow_eq_pow, Real.rpow_one]
      _ = Real.rpow n ((q : ℝ)⁻¹ + 1) := by
        simpa only [Real.rpow_eq_pow] using (Real.rpow_add hnpos _ _).symm
      _ = Real.rpow n (1 + (q : ℝ)⁻¹) := by congr 1 <;> ring
  have hCLog : 0 ≤ C * Real.log n := by
    have : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn))
    positivity
  have hPowerPos : 0 < Real.rpow n (1 + (q : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hnpos _
  calc
    C * input.graph.indepNum * n * Real.log n =
        (C * Real.log n) * ((input.graph.indepNum : ℝ) * n) := by ring
    _ ≤ (C * Real.log n) * Real.rpow n (1 + (q : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hαn hCLog
    _ < Real.rpow n (2 * (q : ℝ)⁻¹) *
        Real.rpow n (1 + (q : ℝ)⁻¹) :=
      mul_lt_mul_of_pos_right hlog hPowerPos
    _ = Real.rpow n ((2 * (q : ℝ)⁻¹) +
        (1 + (q : ℝ)⁻¹)) := by
      simpa only [Real.rpow_eq_pow] using (Real.rpow_add hnpos _ _).symm
    _ = realGapThreshold q n := by
      rw [realGapThreshold]
      congr 1 <;> ring

/-! ### Polynomial resources of the composed program -/

lemma executionOutput_bits_length_add_one_le {n : ℕ}
    (input : GraphCode n) (seed : ExecutionSeed n) :
    (executionOutput input seed).bits.length + 1 ≤ 4 * (n + 1) ^ 4 := by
  have hbase : 1 ≤ n + 1 := by omega
  have hn : n ≤ n + 1 := by omega
  have hn2 : n * n ≤ (n + 1) ^ 4 := by
    calc
      n * n = n ^ 2 := by ring
      _ ≤ (n + 1) ^ 2 := pow_le_pow_left' hn _
      _ ≤ (n + 1) ^ 4 :=
        pow_le_pow_right' hbase (by omega : 2 ≤ 4)
  have hn4 : (n * n) * (n * n) ≤ (n + 1) ^ 4 := by
    calc
      (n * n) * (n * n) = n ^ 4 := by ring
      _ ≤ (n + 1) ^ 4 := pow_le_pow_left' hn _
  have hone : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ hbase
  rw [GraphCode.bits_length]
  omega

lemma approximation_fuel_polynomial {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) {n : ℕ}
    (input : GraphCode n) (seed : ExecutionSeed n) :
    polynomialBound algorithm.program.timeConstant
        algorithm.program.timeExponent (executionOutput input seed).bits.length ≤
      (algorithm.program.timeConstant *
          4 ^ algorithm.program.timeExponent) *
        (n + 1) ^ (4 * algorithm.program.timeExponent) := by
  let k := algorithm.program.timeExponent
  have hlength := executionOutput_bits_length_add_one_le input seed
  unfold polynomialBound
  calc
    algorithm.program.timeConstant *
          ((executionOutput input seed).bits.length + 1) ^ k ≤
        algorithm.program.timeConstant * (4 * (n + 1) ^ 4) ^ k := by
      gcongr
    _ = (algorithm.program.timeConstant * 4 ^ k) *
          (n + 1) ^ (4 * k) := by
      rw [mul_pow, ← pow_mul]
      ring

lemma approximation_output_card_le {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) {n : ℕ}
    (input : GraphCode n) (seed : ExecutionSeed n) :
    (algorithm.output (executionOutput input seed)).card ≤ n * n := by
  simpa using Finset.card_le_card
    (Finset.subset_univ (algorithm.output (executionOutput input seed)))

lemma decoding_steps_polynomial (n : ℕ) :
    (n * n + 1) ^ 2 ≤ 4 * (n + 1) ^ 4 := by
  have hbase : 1 ≤ n + 1 := by omega
  have hn : n ≤ n + 1 := by omega
  have hn2 : n * n ≤ (n + 1) ^ 2 := by
    simpa only [pow_two] using pow_le_pow_left' hn 2
  have hone : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ hbase
  calc
    (n * n + 1) ^ 2 ≤ (2 * (n + 1) ^ 2) ^ 2 := by
      gcongr
      nlinarith
    _ = 4 * (n + 1) ^ 4 := by ring

lemma triangle_gapDecision_steps_polynomial (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) {n : ℕ}
    (input : GraphCode n) (seed : ExecutionSeed n) :
    (gapDecision q n
        (algorithm.output (executionOutput input seed)).card).2 ≤
      (10 * (q + 4) * 4 ^ (q + 5)) *
        (n + 1) ^ (2 * (q + 5)) := by
  let outputCard := (algorithm.output (executionOutput input seed)).card
  let x := n + 1
  have hx : 1 ≤ x := by omega
  have hcard : outputCard ≤ n * n :=
    approximation_output_card_le algorithm input seed
  have hn2 : n * n ≤ x ^ 2 := by
    simpa only [x, pow_two] using
      pow_le_pow_left' (by omega : n ≤ n + 1) 2
  have hnbase : n ≤ x ^ 2 := by
    calc
      n ≤ x := by omega
      _ = x ^ 1 := by simp
      _ ≤ x ^ 2 := pow_le_pow_right' hx (by omega)
  have hbase : n + outputCard + 2 ≤ 4 * x ^ 2 := by
    have hone : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
    nlinarith
  calc
    (gapDecision q n outputCard).2 ≤
        10 * (q + 4) * (n + outputCard + 2) ^ (q + 5) :=
      gapDecision_steps_le q n outputCard
    _ ≤ 10 * (q + 4) * (4 * x ^ 2) ^ (q + 5) := by
      gcongr
    _ = (10 * (q + 4) * 4 ^ (q + 5)) *
          x ^ (2 * (q + 5)) := by
      rw [mul_pow, ← pow_mul]
      ring

/-- Coefficient of one polynomial bound for the fixed composed evaluator. -/
def triangleTimeConstant (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : ℕ :=
  400004 + algorithm.program.timeConstant *
      4 ^ algorithm.program.timeExponent +
    10 * (q + 4) * 4 ^ (q + 5)

/-- Exponent of one polynomial bound for the fixed composed evaluator. -/
def triangleTimeExponent (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : ℕ :=
  20 + 4 * algorithm.program.timeExponent + 2 * (q + 5)

lemma triangleTimeConstant_pos (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) :
    0 < triangleTimeConstant q algorithm := by
  simp [triangleTimeConstant]

/-- The step count returned by the composed evaluator has an explicit polynomial bound. -/
theorem triangleProgram_steps_polynomial (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (n : ℕ)
    (input : GraphCode n) (seed : ExecutionSeed n) :
    (GapProgram.triangleReduction ε algorithm : GapProgram q).steps
        n input seed ≤
      polynomialBound (triangleTimeConstant q algorithm)
        (triangleTimeExponent q algorithm) n := by
  let x := n + 1
  let K := triangleTimeExponent q algorithm
  let approximationConstant := algorithm.program.timeConstant *
    4 ^ algorithm.program.timeExponent
  let decisionConstant := 10 * (q + 4) * 4 ^ (q + 5)
  have hx : 1 ≤ x := by omega
  have h20K : 20 ≤ K := by
    simp only [K, triangleTimeExponent]
    omega
  have h4K : 4 * algorithm.program.timeExponent ≤ K := by
    simp only [K, triangleTimeExponent]
    omega
  have hdecisionK : 2 * (q + 5) ≤ K := by
    simp only [K, triangleTimeExponent]
    omega
  have h4smallK : 4 ≤ K := by omega
  have hexecution : executionSteps input seed ≤ 400000 * x ^ K :=
    (executionSteps_polynomial input seed).trans (by
      exact Nat.mul_le_mul_left 400000 (pow_le_pow_right' hx h20K))
  have happ : polynomialBound algorithm.program.timeConstant
      algorithm.program.timeExponent (executionOutput input seed).bits.length ≤
      approximationConstant * x ^ K :=
    (approximation_fuel_polynomial algorithm input seed).trans (by
      simpa only [approximationConstant] using
        Nat.mul_le_mul_left
          (algorithm.program.timeConstant * 4 ^ algorithm.program.timeExponent)
          (pow_le_pow_right' hx h4K))
  have hdecode : (n * n + 1) ^ 2 ≤ 4 * x ^ K :=
    (decoding_steps_polynomial n).trans (by
      exact Nat.mul_le_mul_left 4 (pow_le_pow_right' hx h4smallK))
  have hdecision : (gapDecision q n
      (algorithm.output (executionOutput input seed)).card).2 ≤
      decisionConstant * x ^ K :=
    (triangle_gapDecision_steps_polynomial q algorithm input seed).trans (by
      simpa only [decisionConstant] using
        Nat.mul_le_mul_left (10 * (q + 4) * 4 ^ (q + 5))
          (pow_le_pow_right' hx hdecisionK))
  simp only [GapProgram.steps]
  unfold polynomialBound
  change executionSteps input seed +
      polynomialBound algorithm.program.timeConstant
        algorithm.program.timeExponent (executionOutput input seed).bits.length +
      (n * n + 1) ^ 2 +
      (gapDecision q n
        (algorithm.output (executionOutput input seed)).card).2 ≤
    triangleTimeConstant q algorithm * x ^ K
  calc
    executionSteps input seed +
          polynomialBound algorithm.program.timeConstant
            algorithm.program.timeExponent (executionOutput input seed).bits.length +
          (n * n + 1) ^ 2 +
          (gapDecision q n
            (algorithm.output (executionOutput input seed)).card).2 ≤
        400000 * x ^ K + approximationConstant * x ^ K +
          4 * x ^ K + decisionConstant * x ^ K := by omega
    _ = triangleTimeConstant q algorithm * x ^ K := by
      simp only [triangleTimeConstant, approximationConstant, decisionConstant]
      ring

lemma triangleProgram_randomBitCount_eq (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (n : ℕ) :
    (GapProgram.triangleReduction ε algorithm : GapProgram q).randomBitCount n =
      finiteRandomBitCount n := by
  rw [GapProgram.randomBitCount, finiteRandomBitCount, card_prefixIndices]
  rfl

theorem triangleProgram_randomBitCount_polynomial (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (n : ℕ) :
    (GapProgram.triangleReduction ε algorithm : GapProgram q).randomBitCount n ≤
      polynomialBound 1400 12 n := by
  rw [triangleProgram_randomBitCount_eq]
  exact finiteRandomBitCount_polynomial n

/-! ### Correctness of the composed gap program -/

lemma triangleProgram_accepts_iff {q : ℕ} (hq : 0 < q) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (n : ℕ)
    (input : GraphCode n) (seed : ExecutionSeed n) :
    (GapProgram.triangleReduction ε algorithm : GapProgram q).accepts
        n input seed = true ↔
      realGapThreshold q n ≤
        (algorithm.output (executionOutput input seed)).card := by
  change (gapDecision q n
    (algorithm.output (executionOutput input seed)).card).1 = true ↔ _
  rw [gapDecision_value, naturalGapThreshold_iff hq]

theorem triangleProgram_completeness (q : ℕ) (hq : 0 < q) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε)
    (hqε : 2 * (q : ℝ)⁻¹ ≤ ε) (n : ℕ) (hn : 1 ≤ n)
    (input : GraphCode n)
    (hhigh : Real.rpow n (1 - (q : ℝ)⁻¹) ≤
      (input.graph.indepNum : ℝ)) :
    2 * ((GapProgram.triangleReduction ε algorithm : GapProgram q).seeds n).card ≤
      3 * ((GapProgram.triangleReduction ε algorithm : GapProgram q).acceptingSeeds
        n input).card := by
  classical
  let program : GapProgram q := GapProgram.triangleReduction ε algorithm
  have hall : ∀ seed ∈ program.seeds n,
      program.accepts n input seed = true := by
    intro seed _
    apply (triangleProgram_accepts_iff hq algorithm n input seed).2
    exact high_output_card algorithm hqε n hn input seed hhigh
  have hfilter :
      (program.seeds n).filter (fun seed ↦ program.accepts n input seed) =
        program.seeds n := Finset.filter_eq_self.2 hall
  change 2 * (program.seeds n).card ≤
    3 * (program.acceptingSeeds n input).card
  unfold GapProgram.acceptingSeeds
  rw [hfilter]
  omega

theorem triangleProgram_soundness (q : ℕ) (hq : 0 < q) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (n : ℕ) (hn : 3 ≤ n)
    (input : GraphCode n)
    (hlow : (input.graph.indepNum : ℝ) ≤ Real.rpow n (q : ℝ)⁻¹)
    (hlog : 40000 * Real.log n < Real.rpow n (2 * (q : ℝ)⁻¹)) :
    3 * ((GapProgram.triangleReduction ε algorithm : GapProgram q).acceptingSeeds
        n input).card ≤
      ((GapProgram.triangleReduction ε algorithm : GapProgram q).seeds n).card := by
  classical
  let program : GapProgram q := GapProgram.triangleReduction ε algorithm
  let failures : Finset (ExecutionSeed n) :=
    (Finset.univ : Finset (ExecutionSeed n)).filter fun seed ↦
      40000 * input.graph.indepNum * n * Real.log n <
        ((executionOutput input seed).graph.indepNum : ℝ)
  have hsubset : program.acceptingSeeds n input ⊆ failures := by
    intro seed hseed
    have haccepts : program.accepts n input seed = true := by
      simpa only [GapProgram.acceptingSeeds, Finset.mem_filter,
        GapProgram.seeds, Finset.mem_univ, true_and] using hseed
    have hacceptsReal : realGapThreshold q n ≤
        (algorithm.output (executionOutput input seed)).card :=
      (triangleProgram_accepts_iff hq algorithm n input seed).1 haccepts
    have hthreshold :
        40000 * input.graph.indepNum * n * Real.log n <
          realGapThreshold q n :=
      low_soundness_threshold 40000 q n (by norm_num) hn input hlow hlog
    have hindependent := algorithm.independent (executionOutput input seed)
      (executionOutput_triangleFree_of_executionSeed input seed)
    have hcard : (algorithm.output (executionOutput input seed)).card ≤
        (executionOutput input seed).graph.indepNum :=
      hindependent.card_le_indepNum
    have hcardReal :
        ((algorithm.output (executionOutput input seed)).card : ℝ) ≤
          (executionOutput input seed).graph.indepNum := by
      exact_mod_cast hcard
    have hfailure := hthreshold.trans_le (hacceptsReal.trans hcardReal)
    have hmem : seed ∈
        ((Finset.univ : Finset (ExecutionSeed n)).filter fun seed ↦
          40000 * input.graph.indepNum * n * Real.log n <
            ((executionOutput input seed).graph.indepNum : ℝ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfailure⟩
    exact hmem
  calc
    3 * (program.acceptingSeeds n input).card ≤ 3 * failures.card :=
      Nat.mul_le_mul_left 3 (Finset.card_le_card hsubset)
    _ ≤ (program.seeds n).card := by
      simpa only [program, failures, GapProgram.seeds] using
        executionSeed_soundness_failure_card_le_third n hn input

/-! ### The certified Håstad-gap solver -/

/-- A cutoff after which the logarithmic loss fits below $n^{2/q}$. -/
noncomputable def gapCutoff (q : ℕ) (hq : 0 < q) : ℕ :=
  max (Classical.choose (exists_log_cutoff 40000 q (by norm_num) hq)) 3

lemma three_le_gapCutoff (q : ℕ) (hq : 0 < q) : 3 ≤ gapCutoff q hq := by
  exact le_max_right _ _

lemma gapCutoff_log (q : ℕ) (hq : 0 < q) (n : ℕ)
    (hn : gapCutoff q hq ≤ n) :
    40000 * Real.log n < Real.rpow n (2 * (q : ℝ)⁻¹) := by
  apply Classical.choose_spec (exists_log_cutoff 40000 q (by norm_num) hq)
  exact (le_max_left _ 3).trans hn

/-- The fixed reduction followed by the supplied approximation solves Håstad's gap. -/
noncomputable def gapSolver (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (hq : 3 ≤ q)
    (hqε : 2 * (q : ℝ)⁻¹ ≤ ε) : MISGapSolver q where
  program := GapProgram.triangleReduction ε algorithm
  timeConstant := triangleTimeConstant q algorithm
  timeExponent := triangleTimeExponent q algorithm
  timeConstant_pos := triangleTimeConstant_pos q algorithm
  timeBound := triangleProgram_steps_polynomial q algorithm
  randomnessConstant := 1400
  randomnessExponent := 12
  randomnessConstant_pos := by norm_num
  randomnessBound := triangleProgram_randomBitCount_polynomial q algorithm
  cutoff := gapCutoff q (by omega)
  completeness := by
    intro n hn input hhigh
    exact triangleProgram_completeness q (by omega) algorithm hqε n
      (by
        have : 3 ≤ n := (three_le_gapCutoff q (by omega)).trans hn
        omega)
      input hhigh
  soundness := by
    intro n hn input hlow
    have hn3 : 3 ≤ n := (three_le_gapCutoff q (by omega)).trans hn
    apply triangleProgram_soundness q (by omega) algorithm n hn3 input hlow
    exact gapCutoff_log q (by omega) n hn

/-- Every positive $ε$ admits an integer gap parameter with $2/q \leq ε$. -/
lemma exists_gap_parameter (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, 3 ≤ q ∧ 2 * (q : ℝ)⁻¹ ≤ ε := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 2 by positivity)
  let q := max (m + 1) 3
  have hmqNat : m + 1 ≤ q := le_max_left _ _
  have hmqReal : ((m + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hmqNat
  have hinverse : (1 : ℝ) / q ≤ 1 / (m + 1 : ℕ) :=
    one_div_le_one_div_of_le (by positivity) hmqReal
  have hm' : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < ε / 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm
  have hqsmall : (1 : ℝ) / q < ε / 2 := hinverse.trans_lt hm'
  refine ⟨q, le_max_right _ _, ?_⟩
  rw [inv_eq_one_div]
  nlinarith [hqsmall]

end Lax47Proofs.GapTransfer
