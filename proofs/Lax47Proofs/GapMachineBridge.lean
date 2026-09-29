import Lax47.Machine
import Lax47Proofs.GapWordEncoding
import Lax253009Proofs.RegisteredBridge.TM2Functions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Lax47Proofs.GapMachineBridge

open Lax253009Proofs Lax253009Proofs.RegisteredBridge
open PCPFoundation.Complexity FiniteEncoding StackEncoding Turing Time
open Lax759944.BinaryWordEncoding (Symbol)
open scoped Classical

/-- The finite-alphabet restriction used by the registered binary compiler
also applies to the three-symbol natural-word encoding. -/
theorem finite_computer {f : List ℕ → List ℕ}
    (M : Turing.TM2ComputableInPolyTime
      Lax759944.BinaryWordEncoding.encode Lax759944.BinaryWordEncoding.encode f) :
    ∃ N : Turing.TM2ComputableInPolyTime
      Lax759944.BinaryWordEncoding.encode Lax759944.BinaryWordEncoding.encode f,
      N.time = M.time ∧ ∀ k, Finite (N.tm.Γ k) := by
  let : Fintype (M.tm.Γ M.tm.k₁) := Fintype.ofEquiv Symbol M.outputAlphabet.symm
  let N : Turing.TM2ComputableInPolyTime
      Lax759944.BinaryWordEncoding.encode Lax759944.BinaryWordEncoding.encode f :=
    { tm := FiniteAlphabet.restrict M.tm
      inputAlphabet := (FiniteAlphabet.inputEquiv M.tm).trans M.inputAlphabet
      outputAlphabet := (FiniteAlphabet.outputEquiv M.tm).trans M.outputAlphabet
      time := M.time
      outputsFun w :=
        { steps := (M.outputsFun w).steps
          steps_le_m := (M.outputsFun w).steps_le_m
          evals_in_steps := by
            have hr := FiniteAlphabet.outputs M.tm
              ((Lax759944.BinaryWordEncoding.encode w).map M.inputAlphabet.symm)
              ((Lax759944.BinaryWordEncoding.encode (f w)).map M.outputAlphabet.symm)
              (M.outputsFun w).steps (Run.of_iterate (M.outputsFun w).evals_in_steps)
            simpa only [List.map_map] using! hr.iterate } }
  exact ⟨N, rfl, FiniteAlphabet.restrict_finite M.tm⟩

theorem packets_injective {A : Type} [Fintype A] :
    Function.Injective (@packets A _) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    have hl := congrArg List.length h
    simp only [packets_length, List.length_nil, mul_zero] at hl
    have : ys.length = 0 := (Nat.mul_eq_zero.mp hl.symm).resolve_left (by omega)
    exact (List.length_eq_zero_iff.mp this).symm
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have hl := congrArg List.length h
      simp only [packets_length, List.length_cons, List.length_nil, mul_zero] at hl
      exact False.elim ((Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))) hl)
    | cons y ys =>
      have hh := congrArg (fun w : List Bool ↦
        (readHead (w.take (Fintype.card A + 1)) : Option A)) h
      simp only [read_head_packets, List.head?_cons, Option.some.injEq] at hh
      subst y
      simp only [packets_cons, List.append_cancel_left_eq] at h
      exact congrArg (List.cons x) (ih h)

/-- Generalized bounded simulation: the encoded initial stacks may have any
polynomial length, rather than being bounded by the raw input length. -/
theorem compile_run_poly {K Λ σ : Type} {Γ : K → Type}
    [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [Nonempty σ]
    [∀ k, Fintype (Γ k)]
    (M : Λ → Turing.TM2.Stmt Γ Λ σ)
    (start : List Bool → Turing.TM2.Cfg Γ Λ σ) (ruler : List Bool → List Bool)
    (hstart : (fun z ↦ encode (start z)) ∈ FP) (hruler : ruler ∈ FP)
    (p : Polynomial ℕ) (hp : ∀ z k, ((start z).stk k).length ≤ p.eval z.length) :
    (fun z ↦ encode ((totalStep M)^[(ruler z).length] (start z))) ∈ FP := by
  obtain ⟨F, hF, hsim⟩ := compile_step M
  obtain ⟨a, b, hab⟩ := encode_length_bound (Γ := Γ) (Λ := Λ) (σ := σ)
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP hruler
  have hsemi : Function.Semiconj encode (totalStep M) F := fun c ↦ (hsim c).symm
  have h := iterate_mem_FP_of_polyBound hF hstart hruler
    (((PolyBound.const a).mul ((PolyBound.eval p).add
      ((PolyBound.const (growth M)).mul (PolyBound.eval q)))).add (PolyBound.const b))
    (fun z t ht ↦ ?bound)
  · exact mem_FP_of_eq h (fun z ↦ (hsemi.iterate_right _ (start z)).symm)
  case bound =>
    rw [← hsemi.iterate_right t (start z)]
    apply hab
    intro k
    exact (total_run_length M (start z) t k).trans
      (Nat.add_le_add (hp z k) (Nat.mul_le_mul_left _ (ht.trans (hq z))))

/-- Inputs assembled from polynomial-time encodings, uniformly in the finite
alphabet chosen by the stack-machine compiler. -/
def EncodedInput (input : List Bool → List ℕ) : Prop :=
  ∀ (A : Type) [Fintype A] (symbol : Symbol → A),
    (fun z ↦ packets ((Lax759944.BinaryWordEncoding.encode (input z)).map symbol)) ∈ FP

theorem init_encoded_input (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]
    (input : List Bool → List (tm.Γ tm.k₀))
    (hinput : (fun z ↦ packets (input z)) ∈ FP) :
    letI : Fintype tm.K := tm.kFin
    letI : Fintype tm.Λ := tm.ΛFin
    letI : Fintype tm.σ := tm.σFin
    (fun z ↦ encode (initList tm (input z))) ∈ FP := by
  let : Fintype tm.K := tm.kFin
  let : Fintype tm.Λ := tm.ΛFin
  let : Fintype tm.σ := tm.σFin
  change (fun z ↦ pair (code (some tm.main, tm.initialState))
    (Cobham.encodeVec fun i : Fin (Fintype.card tm.K) ↦
      packets ((initList tm (input z)).stk ((Fintype.equivFin tm.K).symm i)))) ∈ FP
  apply mem_FP_pair (constFn_mem_FP _)
  apply encodeVec_mem_FP
  intro i
  let k := (Fintype.equivFin tm.K).symm i
  change (fun z ↦ packets ((initList tm (input z)).stk k)) ∈ FP
  by_cases hk : k = tm.k₀
  · have he := congrArg (fun j : tm.K ↦ fun z : List Bool ↦
        packets ((initList tm (input z)).stk j)) hk
    rw [he]
    simpa [initList] using hinput
  · simpa only [initList, dif_neg hk, packets_nil] using constFn_mem_FP []

theorem take_succ_length_eq_iff {α : Type} (a b : List α) :
    a.take (b.length + 1) = b ↔ a = b := by
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_take] at hl
    have ha : a.length ≤ b.length + 1 := by omega
    simpa only [List.take_of_length_le ha] using h
  · rintro rfl
    exact List.take_of_length_le (by omega)

/-- A certified natural-word machine can be called from the binary polynomial
model, provided its encoded input is polynomial-time constructible. -/
theorem accepts_mem_FP {f : List ℕ → List ℕ} {input : List Bool → List ℕ}
    (M : TM2ComputableInPolyTime
      Lax759944.BinaryWordEncoding.encode Lax759944.BinaryWordEncoding.encode f)
    (hinput : EncodedInput input) : FPPred (fun z ↦ f (input z) = [1]) := by
  classical
  obtain ⟨M, _, hfinite⟩ := finite_computer M
  let : Fintype M.tm.K := M.tm.kFin
  let : Fintype M.tm.Λ := M.tm.ΛFin
  let : Fintype M.tm.σ := M.tm.σFin
  let (k : M.tm.K) : Fintype (M.tm.Γ k) := Fintype.ofFinite (M.tm.Γ k)
  let ins := fun z ↦ (Lax759944.BinaryWordEncoding.encode (input z)).map M.inputAlphabet.symm
  have hins : (fun z ↦ packets (ins z)) ∈ FP := hinput _ _
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hins
  have hlen (z) : (Lax759944.BinaryWordEncoding.encode (input z)).length ≤ p.eval z.length := by
    have h := hp z
    simp only [packets_length, ins, List.length_map] at h
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans h
  obtain ⟨ruler, hruler, hrlen⟩ := Cobham.exists_ruler (M.time.comp p)
  have hrun := compile_run_poly M.tm.m
    (fun z ↦ initList M.tm (ins z)) ruler (init_encoded_input M.tm ins hins) hruler p
    (fun z k ↦ ?_)
  · have hout := mem_FP_comp hrun (stack_mem_FP M.tm.k₁)
    let target := packets ((Lax759944.BinaryWordEncoding.encode [1]).map M.outputAlphabet.symm)
    have ht := FPPred.of_bounded_key (take_mem_FP hout (target.length + 1))
      (fun _ ↦ List.length_take_le _ _) (fun key ↦ key = target)
    apply ht.of_iff
    intro z
    have h := M.outputsFun (input z)
    have hs : (totalStep M.tm.m)^[(ruler z).length] (initList M.tm (ins z)) =
        haltList M.tm ((Lax759944.BinaryWordEncoding.encode (f (input z))).map M.outputAlphabet.symm) :=
      total_run_after_halt M.tm.m h.evals_in_steps rfl
        (h.steps_le_m.trans ((polynomial_eval_mono_nat M.time (hlen z)).trans
          (by simpa only [Polynomial.eval_comp] using hrlen z)))
    dsimp only [Function.comp_apply] at ht ⊢
    rw [hs, stack_encode]
    simp only [haltList, take_succ_length_eq_iff]
    change packets ((Lax759944.BinaryWordEncoding.encode (f (input z))).map M.outputAlphabet.symm) =
      packets ((Lax759944.BinaryWordEncoding.encode [1]).map M.outputAlphabet.symm) ↔ _
    rw [packets_injective.eq_iff, List.map_inj_right M.outputAlphabet.symm.injective]
    exact GapWordEncoding.encode_singleton_one_iff _
  · by_cases hk : k = M.tm.k₀
    · subst k
      simpa [initList, ins] using hlen z
    · simp [initList, hk]

end Lax47Proofs.GapMachineBridge
