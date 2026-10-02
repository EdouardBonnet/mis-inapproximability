import Lax614640.Machine
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card

/-!
---
title: Executable graph encodings and triangle-free approximation
type: definition
---
Graphs are finite Boolean adjacency matrices with symmetry and looplessness
certificates.  Their machine word is the vertex count followed by the complete
row-major matrix, with Booleans encoded by $0$ and $1$.  An approximation is a
function certified polynomial-time by the Lax759944 finite-Turing model; its
returned independent set is decoded from that certified function.
-/

set_option autoImplicit false

namespace Lax614640.Complexity

open Lax614640.Machine

export Lax614640.Machine
  (BitString RandomSeed PolytimeProgram polynomialBound pairBits)

/-- An executable simple graph on the labeled vertex set $\operatorname{Fin}(n)$. -/
structure GraphCode (n : ℕ) where
  adjacent : Fin n → Fin n → Bool
  loopless : ∀ vertex, adjacent vertex vertex = false
  symmetric : ∀ left right, adjacent left right = adjacent right left

/-- The mathematical simple graph represented by a Boolean adjacency matrix. -/
def GraphCode.graph {n : ℕ} (code : GraphCode n) : SimpleGraph (Fin n) where
  Adj left right := code.adjacent left right = true
  symm := ⟨fun left right h ↦ (code.symmetric left right).symm.trans h⟩
  loopless := ⟨fun vertex h ↦ Bool.noConfusion ((code.loopless vertex).symm.trans h)⟩

/-- Vertex count followed by the row-major adjacency matrix. -/
def GraphCode.bits {n : ℕ} (code : GraphCode n) : BitString :=
  n :: List.ofFn fun rank : Fin (n * n) ↦
    let vertex := finProdFinEquiv.symm rank
    bitWord (code.adjacent vertex.1 vertex.2)

/-- Decode the first $n$ output bits as a vertex set. -/
def decodeVertexSet (n : ℕ) (bits : BitString) : Finset (Fin n) :=
  Finset.univ.filter fun vertex ↦ bits[vertex.1]? = some 1

/-- A polynomial-time executable approximation for triangle-free Max Independent Set. -/
structure TriangleFreeMISApproximation (ε : ℝ) where
  program : PolytimeProgram
  correctness : ∀ (n : ℕ) (code : GraphCode n),
    code.graph.CliqueFree 3 →
    let set := decodeVertexSet n (program.output code.bits)
    code.graph.IsIndepSet set ∧
      (code.graph.indepNum : ℝ) ≤
      Real.rpow n ((1 : ℝ) / 2 - ε) * set.card

/-- Max Independent Set on triangle-free graphs admits a polynomial-time
$n^{1/2-\varepsilon}$-approximation. -/
def TriangleFreeMISApproximable (ε : ℝ) : Prop :=
  Nonempty (TriangleFreeMISApproximation ε)

end Lax614640.Complexity
