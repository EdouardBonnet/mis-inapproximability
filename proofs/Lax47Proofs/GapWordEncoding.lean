import Lax47.Machine
import Lax253009Proofs.PCPFoundation.Mathlib.NatBits
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

set_option autoImplicit false

namespace Lax47Proofs.GapWordEncoding

open Lax759944.BinaryWordEncoding

theorem count_separator_encodeNat (n : ℕ) :
    (encodeNat n).count Symbol.separator = 1 := by
  have h : Symbol.separator ∉ n.bits.map (fun b ↦ if b then Symbol.one else Symbol.zero) := by
    simp only [List.mem_map]
    rintro ⟨b, _, hb⟩
    cases b <;> simp at hb
  simp [encodeNat, List.count_eq_zero.mpr h]

theorem count_separator_encode (w : List ℕ) :
    (encode w).count Symbol.separator = w.length := by
  induction w with
  | nil => simp [encode]
  | cons a w ih =>
    change (encodeNat a ++ encode w).count Symbol.separator = (a :: w).length
    simp [count_separator_encodeNat, ih, Nat.add_comm]

theorem encode_singleton_one_iff (w : List ℕ) :
    encode w = encode [1] ↔ w = [1] := by
  constructor
  · intro h
    have hc := congrArg (List.count Symbol.separator) h
    simp only [count_separator_encode, List.length_singleton] at hc
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hc
    have he : n.bits = (1 : ℕ).bits := by
      have hm : n.bits.map (fun b ↦ if b then Symbol.one else Symbol.zero) =
          (1 : ℕ).bits.map (fun b ↦ if b then Symbol.one else Symbol.zero) := by
        simpa [encode, encodeNat] using h
      exact (List.map_inj_right (by intro a b hab; cases a <;> cases b <;> simp_all)).mp hm
    have hn : n = 1 := by
      have hh := congrArg Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE he
      simpa only [Lax253009Proofs.PCPFoundation.BinaryNat.fromBitsLE_bits] using hh
    simp [hn]
  · rintro rfl
    rfl

end Lax47Proofs.GapWordEncoding
