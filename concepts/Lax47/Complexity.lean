import Lax47.Machine
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card

/-!
---
title: Executable graph encodings and triangle-free approximation
type: definition
---
Graphs are finite Boolean adjacency matrices with symmetry and looplessness
certificates.  Their machine encoding is the unary vertex count followed by
the complete row-major matrix.  An approximation is a binary Turing program;
its returned independent set is decoded from the program's actual output
bits.  No Lean function supplies a separate semantic answer or a detached
running-time annotation.
-/

set_option autoImplicit false

namespace Lax47.Complexity

open Lax47.Machine

export Lax47.Machine
  (BitString Language RandomSeed PolytimeProgram NPVerifier BPPAlgorithm
    InNP InBPP NPSubsetBPP polynomialBound pairBits)

/-- An executable simple graph on the labeled vertex set $\operatorname{Fin}(n)$. -/
structure GraphCode (n : ℕ) where
  adjacent : Fin n → Fin n → Bool
  loopless : ∀ vertex, adjacent vertex vertex = false
  symmetric : ∀ left right, adjacent left right = adjacent right left

/-- The mathematical simple graph represented by a Boolean adjacency matrix. -/
def GraphCode.graph {n : ℕ} (code : GraphCode n) : SimpleGraph (Fin n) where
  Adj left right := code.adjacent left right = true
  symm left right h := by
    change code.adjacent right left = true
    rw [← code.symmetric]
    exact h
  loopless := ⟨fun vertex ↦ by
    simp [code.loopless]⟩

@[simp] lemma GraphCode.graph_adj {n : ℕ} (code : GraphCode n)
    (left right : Fin n) :
    code.graph.Adj left right ↔ code.adjacent left right = true :=
  Iff.rfl

/-- Unary length followed by the row-major adjacency matrix. -/
def GraphCode.bits {n : ℕ} (code : GraphCode n) : BitString :=
  List.replicate n true ++ false ::
    (List.ofFn fun left : Fin n ↦
      List.ofFn fun right : Fin n ↦ code.adjacent left right).flatten

lemma GraphCode.bits_length {n : ℕ} (code : GraphCode n) :
    code.bits.length = n + 1 + n * n := by
  have hrows :
      List.map List.length
          (List.ofFn fun left : Fin n ↦
            List.ofFn fun right : Fin n ↦ code.adjacent left right) =
        List.replicate n n := by
    rw [List.map_ofFn]
    rw [← List.ofFn_const]
    congr 1
    funext left
    simp
  unfold GraphCode.bits
  rw [List.length_append, List.length_replicate, List.length_cons,
    List.length_flatten, hrows, List.sum_replicate]
  simp [Nat.add_comm, Nat.add_left_comm]

/-- The edgeless executable graph. -/
def GraphCode.empty (n : ℕ) : GraphCode n where
  adjacent := fun _ _ ↦ false
  loopless := by simp
  symmetric := by simp

/-- Decode the first $n$ output bits as a vertex set. -/
def decodeVertexSet (n : ℕ) (bits : BitString) : Finset (Fin n) :=
  Finset.univ.filter fun vertex ↦ bits[vertex.1]? = some true

/-- A polynomial-time executable approximation for triangle-free Max Independent Set. -/
structure TriangleFreeMISApproximation (ε : ℝ) where
  program : PolytimeProgram
  correctness : ∀ (n : ℕ) (code : GraphCode n),
    code.graph.CliqueFree 3 →
    let set := decodeVertexSet n (program.output code.bits)
    code.graph.IsIndepSet set ∧
      (code.graph.indepNum : ℝ) ≤
        Real.rpow n ((1 : ℝ) / 2 - ε) * set.card

/-- The vertex set decoded from the certified machine's output. -/
def TriangleFreeMISApproximation.output
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    {n : ℕ} (code : GraphCode n) : Finset (Fin n) :=
  decodeVertexSet n (algorithm.program.output code.bits)

/-- The decoded output is independent on every triangle-free input. -/
theorem TriangleFreeMISApproximation.independent
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    {n : ℕ} (code : GraphCode n) (triangleFree : code.graph.CliqueFree 3) :
    code.graph.IsIndepSet (algorithm.output code) :=
  (algorithm.correctness n code triangleFree).1

/-- The decoded output has the claimed approximation ratio. -/
theorem TriangleFreeMISApproximation.approximation
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    {n : ℕ} (code : GraphCode n) (triangleFree : code.graph.CliqueFree 3) :
    (code.graph.indepNum : ℝ) ≤
      Real.rpow n ((1 : ℝ) / 2 - ε) * (algorithm.output code).card :=
  (algorithm.correctness n code triangleFree).2

end Lax47.Complexity
