import Lax614640Proofs.GapMachineBridge
import Lax614640Proofs.GapComparison
import Lax253009Proofs.PCPFoundation.Classes.P.NatCodes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Lax614640Proofs.GapInput

open Lax253009Proofs Lax253009Proofs.RegisteredBridge
open PCPFoundation.Complexity FiniteEncoding Lax759944.BinaryWordEncoding
open Lax614640.Machine Lax614640.Complexity GapMachineBridge
open scoped Classical

theorem encoded_cons {n : List Bool → ℕ} {w : List Bool → List ℕ}
    (hn : UnaryFn n) (hw : EncodedInput w) : EncodedInput (fun z ↦ n z :: w z) := by
  intro A _ symbol
  have hb := mem_FP_comp (bits_mem_FP hn)
    (packets_map_mem_FP (fun b ↦ symbol (if b then Symbol.one else Symbol.zero)))
  have hh := Cobham.appendFn_mem_FP (constFn_mem_FP (packet (symbol Symbol.separator))) hb
  apply mem_FP_of_eq (Cobham.appendFn_mem_FP hh (hw A symbol))
  intro z
  simp [Lax759944.BinaryWordEncoding.encode, encodeNat, packets, List.map_flatMap,
    List.flatMap_map, List.flatMap_append, List.map_append]

theorem encoded_append {u v : List Bool → List ℕ}
    (hu : EncodedInput u) (hv : EncodedInput v) : EncodedInput (fun z ↦ u z ++ v z) := by
  intro A _ symbol
  apply mem_FP_of_eq (Cobham.appendFn_mem_FP (hu A symbol) (hv A symbol))
  intro z
  simp [Lax759944.BinaryWordEncoding.encode, packets, List.flatMap_append, List.map_append]

theorem encoded_bits {w : List Bool → List Bool} (hw : w ∈ FP) :
    EncodedInput (fun z ↦ (w z).map bitWord) := by
  intro A _ symbol
  have h := mem_FP_comp hw (flatMap_mem_FP (fun b ↦ packets ((encodeNat (bitWord b)).map symbol)))
  apply mem_FP_of_eq h
  intro z
  simp [Lax759944.BinaryWordEncoding.encode, packets, List.flatMap_map, List.map_flatMap,
    List.flatMap_assoc]

def order (w : List Bool) : ℕ := (w.takeWhile id).length

theorem header_poly : (fun w : List Bool ↦ w.takeWhile id) ∈ FP := by
  let state := pairSnd ∘ pairFst
  have hstate : state ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  refine recFold_mem_FP_of_bound
    (g := fun _ t ↦ t.takeWhile id)
    (constFn_mem_FP [])
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true]) hstate)
    (constFn_mem_FP []) (constFn_mem_FP []) id_mem_FP
    (fun _ ↦ rfl) ?_ ?_ PolyBound.id ?_
  · intro z t
    simp
  · intro z t
    simp [state]
  · intro z t ht
    exact (List.takeWhile_sublist (l := t) id).length_le.trans ht.length_le

theorem order_poly : UnaryFn order := UnaryFn.length header_poly

@[simp] theorem order_encode {n : ℕ} (G : Lax253009.Graphs.Graph n) : order G.encode = n := by
  simp [order, Lax253009.Graphs.Graph.encode]

def bitAt (w : List Bool) (i : ℕ) : Bool := ((w.drop i).head?).getD false

theorem bitAt_poly {w : List Bool → List Bool} {i : List Bool → ℕ}
    (hw : w ∈ FP) (hi : UnaryFn i) : FPPred (fun z ↦ bitAt (w z) (i z) = true) := by
  have hd := dropLenFn_mem_FP hi.mem_FP hw
  have h := bounded_read_mem_FP hd 1 (fun key ↦ [key.head?.getD false])
  apply (FPPred.of_flag h).of_iff
  intro z
  simp only [List.length_replicate, bitAt]
  cases (w z).drop (i z) <;> rfl

def matrix (w : List Bool) : List Bool :=
  (List.range (order w * order w)).map fun i ↦
    decide (i / order w ≠ i % order w) && !bitAt w (order w + 1 + i)

theorem matrix_poly : matrix ∈ FP := by
  have hn := order_poly.lift
  have hi := UnaryFn.index
  have he := (FPPred.eq (hi.div hn) (hi.mod hn)).not
  have hb := bitAt_poly pairFst_mem_FP ((hn.add (UnaryFn.const 1)).add hi)
  have hf := (he.and hb.not).flag_mem_FP
  apply mem_FP_of_eq (bitwise_mem_FP (order_poly.mul order_poly) hf (fun _ _ ↦ ?_))
  · intro z
    rfl
  · simp [pairFst_pair, pairSnd_pair, List.length_replicate, Bool.not_eq_true]

def solverInput (z : List Bool) : List ℕ :=
  pairBits (order (pairFst z) :: (matrix (pairFst z)).map bitWord)
    ((pairSnd z).map bitWord)

theorem solverInput_poly : EncodedInput solverInput := by
  have hm := mem_FP_comp pairFst_mem_FP matrix_poly
  have hn := order_poly.comp pairFst_mem_FP
  have hp := (hn.mul hn).add (UnaryFn.const 1)
  have h := encoded_cons hp
    (encoded_append (encoded_cons hn (encoded_bits hm)) (encoded_bits pairSnd_mem_FP))
  intro A _ symbol
  apply mem_FP_of_eq (h A symbol)
  intro z
  simp [solverInput, pairBits, matrix, Nat.add_comm]

theorem rowMajor {α : Type} {n : ℕ} (f : Fin n → Fin n → α) :
    (List.finRange n).flatMap (fun u ↦ (List.finRange n).map (f u)) =
      List.ofFn (fun i : Fin (n * n) ↦ f (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2) := by
  rw [List.ofFn_mul]
  simp only [List.ofFn_eq_map, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro u _
  apply List.map_congr_left
  intro v _
  have hn : 0 < n := Nat.zero_lt_of_lt v.isLt
  simp [finProdFinEquiv, Fin.divNat, Fin.modNat, Nat.mod_eq_of_lt v.isLt]
  congr 1
  apply Fin.ext
  change u.val = (u.val * n + v.val) / n
  rw [Nat.mul_comm, Nat.mul_add_div hn]
  simp [Nat.div_eq_of_lt v.isLt]

theorem bitAt_encode {n : ℕ} (G : Lax253009.Graphs.Graph n) (i : Fin (n * n)) :
    bitAt G.encode (n + 1 + i.val) =
      G.adjacent (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
  have hd : G.encode.drop (n + 1) = List.ofFn (fun i : Fin (n * n) ↦
      G.adjacent (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) := by
    simp [Lax253009.Graphs.Graph.encode, rowMajor, List.drop_append]
  unfold bitAt
  rw [← List.drop_drop, hd]
  simp

theorem matrix_encode {n : ℕ} (G : Lax253009.Graphs.Graph n) :
    matrix G.encode = List.ofFn (fun i : Fin (n * n) ↦
      (GapComparison.complement G).adjacent (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2) := by
  unfold matrix
  rw [order_encode]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hi0 : i < n * n := by simpa using hi'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [bitAt_encode G ⟨i, hi0⟩]
    simp [GapComparison.complement, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]

theorem solverInput_encode {n : ℕ} (G : Lax253009.Graphs.Graph n) (r : List Bool) :
    solverInput (pair G.encode r) = pairBits (GapComparison.complement G).bits (r.map bitWord) := by
  simp [solverInput, matrix_encode, GraphCode.bits, List.map_ofFn, Function.comp_def]

end Lax614640Proofs.GapInput
