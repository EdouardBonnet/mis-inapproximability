import Lax47Proofs.GapInput
import Lax253009Proofs.RegisteredBridge.BoundedErrorTests
import Lax253009Proofs.RegisteredBridge.RandomizedApproximationTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Lax47Proofs.GapTest

open Lax253009Proofs Lax253009Proofs.RegisteredBridge
open PCPFoundation.Complexity FiniteEncoding BoundedErrorTests
open Lax253009.Graphs Lax47.Gap Lax47.Machine GapInput GapMachineBridge
open scoped Classical

theorem graph_encoding_injective : Function.Injective (fun g : Σ n, Graph n ↦ g.2.encode) := by
  rintro ⟨n, G⟩ ⟨m, H⟩ he
  have hn : n = m := by simpa using congrArg order he
  subst m
  have ha : G.adjacent = H.adjacent := by
    funext u v
    have hh := congrArg (fun w ↦ GapInput.bitAt w (n + 1 + (finProdFinEquiv (u,v)).val)) he
    simpa only [bitAt_encode, Equiv.symm_apply_apply] using hh
  have hg : G = H := by cases G; cases H; cases ha; rfl
  subst H
  rfl

noncomputable def cliqueOf (w : List Bool) : ℕ :=
  if h : ∃ g : Σ n, Graph n, g.2.encode = w then h.choose.2.cliqueNumber else 0

@[simp] theorem cliqueOf_encode {n : ℕ} (G : Graph n) : cliqueOf G.encode = G.cliqueNumber := by
  unfold cliqueOf
  rw [dif_pos (show ∃ g : Σ n, Graph n, g.2.encode = G.encode from ⟨⟨n,G⟩, rfl⟩)]
  have h : Classical.choose (show ∃ g : Σ n, Graph n, g.2.encode = G.encode from ⟨⟨n,G⟩, rfl⟩) =
      ⟨n, G⟩ := graph_encoding_injective
    (Classical.choose_spec (show ∃ g : Σ n, Graph n, g.2.encode = G.encode from ⟨⟨n,G⟩, rfl⟩))
  exact congrArg (fun g : Σ n, Graph n ↦ g.2.cliqueNumber) h

def smallBound (N : ℕ) : ℕ := N + 1 + N * N

noncomputable def smallClique (N : ℕ) (w : List Bool) : ℕ := cliqueOf (w.take (smallBound N))

theorem smallClique_poly (N : ℕ) : UnaryFn (smallClique N) := by
  exact mem_FP_of_bounded_key (take_mem_FP id_mem_FP (smallBound N))
    (fun _ ↦ List.length_take_le _ _) (fun key ↦ List.replicate (cliqueOf key) true)

theorem smallClique_encode {n N : ℕ} (G : Graph n) (hn : n ≤ N) :
    smallClique N G.encode = G.cliqueNumber := by
  have hl : G.encode.length = n + 1 + n * n := by
    simp only [Graph.encode, rowMajor, List.length_append, List.length_replicate,
      List.length_singleton, List.length_ofFn]
  unfold smallClique
  rw [List.take_of_length_le (by rw [hl]; unfold smallBound; nlinarith), cliqueOf_encode]

theorem unary_pow {n : List Bool → ℕ} (hn : UnaryFn n) (k : ℕ) :
    UnaryFn (fun z ↦ n z ^ k) := by
  induction k with
  | zero => simpa using UnaryFn.const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hn

noncomputable def answer {q : ℕ} (S : MISGapSolver q) (z : List Bool) : Bool :=
  let g := pairFst (pairFst z)
  let k := (pairSnd (pairFst z)).length
  let n := order g
  if n < S.cutoff then decide (k ≤ smallClique S.cutoff g)
  else if k = 0 then true
  else if k ^ q ≤ n then
    decide (S.program.program.output (solverInput (pair g (pairSnd z))) = [1])
  else false

theorem answer_poly {q : ℕ} (S : MISGapSolver q) : FPPred (fun z ↦ answer S z = true) := by
  have hg := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hk := UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hn := order_poly.comp hg
  have hs := FPPred.lt hn (UnaryFn.const S.cutoff)
  have hsmall := FPPred.le hk ((smallClique_poly S.cutoff).comp hg)
  have hz := FPPred.eq hk (UnaryFn.const 0)
  have hguard := FPPred.le (unary_pow hk q) hn
  obtain ⟨M⟩ := S.program.program.polytime
  have hm := accepts_mem_FP M solverInput_poly
  have hcall := hm.comp (mem_FP_pair hg pairSnd_mem_FP)
  have h := hs.ite_mem_FP hsmall.flag_mem_FP
    (hz.ite_mem_FP (constFn_mem_FP [true])
      (hguard.ite_mem_FP hcall.flag_mem_FP (constFn_mem_FP [false])))
  apply (FPPred.of_flag (v := answer S) ?_)
  apply mem_FP_of_eq h
  intro z
  simp only [answer, Function.comp_apply]
  split_ifs <;> rfl

noncomputable def test {q : ℕ} (S : MISGapSolver q) : Test where
  bits := fun y ↦ S.program.randomBitCount (order (pairFst y))
  bits_poly := (UnaryFn.const S.program.randomnessConstant).mul
    (unary_pow ((order_poly.comp pairFst_mem_FP).add (UnaryFn.const 1))
      S.program.randomnessExponent)
  answer := answer S
  answer_poly := answer_poly S

theorem answer_encode {q n : ℕ} (S : MISGapSolver q) (G : Graph n) (k : ℕ)
    (r : S.program.Seed n) :
    answer S (pair (pair G.encode (List.replicate k false)) (List.ofFn r)) =
      GapComparison.classify S G k r := by
  simp only [answer, pairFst_pair, pairSnd_pair, List.length_replicate, order_encode,
    solverInput_encode, GapComparison.classify]
  by_cases hn : n < S.cutoff
  · simp [hn, smallClique_encode G (Nat.le_of_lt hn)]
  · simp only [hn, if_false]
    rfl

theorem error_encode {q n : ℕ} (S : MISGapSolver q) (G : Graph n) (k : ℕ) (b : Bool) :
    (test S).error (pair G.encode (List.replicate k false)) b =
      Lax253009.FiniteProbability.probability (fun r : S.program.Seed n ↦
        GapComparison.classify S G k r ≠ b) := by
  rw [← RandomizedApproximationTest.tape_error (test S) _ b (S.program.randomBitCount n)
    (by simp [test])]
  simp only [test, answer_encode]

theorem complete_error {q n : ℕ} (S : MISGapSolver q) (G : Graph n) (k : ℕ)
    (hn : 0 < n) (hq : 0 < q)
    (hh : Real.rpow (n : ℝ) (1 - (q : ℝ)⁻¹) * k < G.cliqueNumber) :
    (test S).error (pair G.encode (List.replicate k false)) true ≤ 1 / 3 := by
  rw [error_encode, FairTests.probability_not]
  have h := GapComparison.classify_complete S G k hn hq hh
  linarith

theorem sound_error {q n : ℕ} (S : MISGapSolver q) (G : Graph n) (k : ℕ)
    (hq : 0 < q) (hh : G.cliqueNumber < k) :
    (test S).error (pair G.encode (List.replicate k false)) false ≤ 1 / 3 := by
  rw [error_encode]
  simpa only [Bool.not_eq_false] using GapComparison.classify_sound S G k hq hh

end Lax47Proofs.GapTest
