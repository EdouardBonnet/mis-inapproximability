import Lax614640.Gap
import Lax253009.Graphs
import Lax253009.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax614640Proofs.GapComparison

open Lax614640.Complexity Lax253009.Graphs

/-- Complement the clique instance before calling the independent-set solver. -/
def complement {n : ℕ} (G : Graph n) : GraphCode n where
  adjacent u v := decide (u ≠ v) && !G.adjacent u v
  loopless v := by simp
  symmetric u v := by simp [ne_comm, G.symmetric]

theorem complement_graph {n : ℕ} (G : Graph n) :
    (complement G).graph = G.simpleGraphᶜ := by
  ext u v
  simp [GraphCode.graph, complement, Graph.simpleGraph, SimpleGraph.compl_adj]

@[simp] theorem complement_indepNum {n : ℕ} (G : Graph n) :
    (complement G).graph.indepNum = G.cliqueNumber := by
  rw [complement_graph, SimpleGraph.indepNum_compl]
  rfl

theorem cliqueNumber_le {n : ℕ} (G : Graph n) : G.cliqueNumber ≤ n := by
  obtain ⟨s, hs⟩ := G.simpleGraph.exists_isNClique_cliqueNum
  have h := Finset.card_le_univ s
  simpa [hs.card_eq, Graph.cliqueNumber] using h

/-- A positive threshold in the relative completeness gap already gives the
absolute high promise. -/
theorem high_promise {n k a q : ℕ} (hk : 0 < k)
    (h : Real.rpow (n : ℝ) (1 - (q : ℝ)⁻¹) * k < a) :
    Real.rpow (n : ℝ) (1 - (q : ℝ)⁻¹) ≤ a := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp := Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (q : ℝ)⁻¹)
  nlinarith

/-- The threshold guard supplies the absolute low promise on sound instances. -/
theorem low_promise {n k a q : ℕ} (hq : 0 < q) (hk : k ^ q ≤ n)
    (ha : a < k) : (a : ℝ) ≤ Real.rpow (n : ℝ) (q : ℝ)⁻¹ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hkn : (k : ℝ) ^ q ≤ n := by exact_mod_cast hk
  have hroot := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ q)
    hkn (inv_nonneg.mpr hq'.le)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k),
    mul_inv_cancel₀ (ne_of_gt hq'), Real.rpow_one] at hroot
  exact (by exact_mod_cast ha.le : (a : ℝ) ≤ k).trans hroot

/-- Completeness forces the guard to pass: a clique cannot exceed the order
of its graph. -/
theorem threshold_guard {n k a q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (ha : a ≤ n)
    (h : Real.rpow (n : ℝ) (1 - (q : ℝ)⁻¹) * k < a) : k ^ q ≤ n := by
  simp only [Real.rpow_eq_pow] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp := Real.rpow_pos_of_pos hn' (1 - (q : ℝ)⁻¹)
  have hmul : (n : ℝ) ^ (1 - (q : ℝ)⁻¹) *
      (n : ℝ) ^ (q : ℝ)⁻¹ = n := by
    rw [← Real.rpow_add hn']
    simp
  have hk : (k : ℝ) < (n : ℝ) ^ (q : ℝ)⁻¹ := by
    have ha' : (a : ℝ) ≤ n := by exact_mod_cast ha
    nlinarith
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg k) hk.le q
  simp_rw [← Real.rpow_natCast] at hb
  rw [← Real.rpow_mul hn'.le,
    inv_mul_cancel₀ (ne_of_gt hq'), Real.rpow_one] at hb
  exact_mod_cast hb

open Lax614640.Gap Lax253009.FiniteProbability
open scoped Classical

/-- On small graphs use exhaustive search; otherwise guard the threshold and
call the supplied solver on the complement. -/
noncomputable def classify {q : ℕ} (S : MISGapSolver q) {n : ℕ}
    (G : Graph n) (k : ℕ) (r : S.program.Seed n) : Bool :=
  if n < S.cutoff then decide (k ≤ G.cliqueNumber)
  else if k = 0 then true
  else if k ^ q ≤ n then S.program.accepts n (complement G) r
  else false

theorem solver_complete {q n : ℕ} (S : MISGapSolver q) (G : Graph n)
    (hn : S.cutoff ≤ n)
    (hh : Real.rpow (n : ℝ) (1 - (q : ℝ)⁻¹) ≤ G.cliqueNumber) :
    (2 / 3 : ℝ) ≤ probability (fun r ↦ S.program.accepts n (complement G) r = true) := by
  classical
  have h := S.completeness n hn (complement G) (by simpa using hh)
  have hp : (0 : ℝ) < Fintype.card (S.program.Seed n) := by
    exact_mod_cast Fintype.card_pos
  unfold probability
  apply (div_le_div_iff₀ (by norm_num) hp).mpr
  have hc : 2 * (Fintype.card (S.program.Seed n) : ℝ) ≤
      3 * ((Finset.univ.filter (fun r ↦ S.program.accepts n (complement G) r = true)).card : ℝ) := by
    exact_mod_cast h
  convert hc using 1 <;> (try simp only [mul_comm]) <;> congr! 6

theorem solver_sound {q n : ℕ} (S : MISGapSolver q) (G : Graph n)
    (hn : S.cutoff ≤ n)
    (hh : (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (q : ℝ)⁻¹) :
    probability (fun r ↦ S.program.accepts n (complement G) r = true) ≤ (1 / 3 : ℝ) := by
  classical
  have h := S.soundness n hn (complement G) (by simpa using hh)
  have hp : (0 : ℝ) < Fintype.card (S.program.Seed n) := by
    exact_mod_cast Fintype.card_pos
  unfold probability
  apply (div_le_div_iff₀ hp (by norm_num)).mpr
  have hc : 3 * ((Finset.univ.filter (fun r ↦ S.program.accepts n (complement G) r = true)).card : ℝ) ≤
      (Fintype.card (S.program.Seed n) : ℝ) := by exact_mod_cast h
  convert hc using 1 <;> (try simp only [one_mul, mul_comm]) <;> congr! 6

theorem classify_complete {q n : ℕ} (S : MISGapSolver q) (G : Graph n)
    (k : ℕ) (hn : 0 < n) (hq : 0 < q)
    (hh : Real.rpow (n : ℝ) (1 - (q : ℝ)⁻¹) * k < G.cliqueNumber) :
    (2 / 3 : ℝ) ≤ probability (fun r ↦ classify S G k r = true) := by
  have hp : (0 : ℝ) < Fintype.card (S.program.Seed n) := by
    exact_mod_cast Fintype.card_pos
  by_cases hs : n < S.cutoff
  · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hi : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq'
    have hf : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 - (q : ℝ)⁻¹) := by
      exact Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
    have hk : k ≤ G.cliqueNumber := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hkr : (k : ℝ) ≤ G.cliqueNumber := by nlinarith
      exact_mod_cast hkr
    norm_num [classify, hs, hk, probability]
  · by_cases hk : k = 0
    · norm_num [classify, hs, hk, probability]
    · have hg := threshold_guard hn hq (cliqueNumber_le G) hh
      simpa only [classify, hs, if_false, hk, hg, if_true] using
        solver_complete S G (Nat.le_of_not_gt hs) (high_promise (Nat.pos_of_ne_zero hk) hh)

theorem classify_sound {q n : ℕ} (S : MISGapSolver q) (G : Graph n)
    (k : ℕ) (hq : 0 < q) (hh : G.cliqueNumber < k) :
    probability (fun r ↦ classify S G k r = true) ≤ (1 / 3 : ℝ) := by
  by_cases hs : n < S.cutoff
  · simp [classify, hs, Nat.not_le_of_lt hh, probability]
  · have hk : k ≠ 0 := by omega
    by_cases hg : k ^ q ≤ n
    · simpa only [classify, hs, if_false, hk, hg, if_true] using
        solver_sound S G (Nat.le_of_not_gt hs) (low_promise hq hg hh)
    · simp [classify, hs, hk, hg, probability]

end Lax614640Proofs.GapComparison
