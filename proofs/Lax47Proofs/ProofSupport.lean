import Lax47.Gap

set_option autoImplicit false

namespace Lax47Proofs

open Lax47.Machine Lax47.Complexity

/-!
Proof-only conveniences derived from the public complexity interfaces.  None
of these declarations occurs in the semantic closure of the main theorem.
-/

@[simp] lemma graphCode_graph_adj {n : ℕ} (code : GraphCode n)
    (left right : Fin n) :
    code.graph.Adj left right ↔ code.adjacent left right = true :=
  Iff.rfl

lemma graphCode_bits_length {n : ℕ} (code : GraphCode n) :
    code.bits.length = 1 + n * n := by
  simp [GraphCode.bits, Nat.add_comm]

/-- The vertex set decoded from a certified approximation program's output. -/
def approximationOutput
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    {n : ℕ} (code : GraphCode n) : Finset (Fin n) :=
  decodeVertexSet n (algorithm.program.output code.bits)

theorem approximationOutput_independent
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    {n : ℕ} (code : GraphCode n) (triangleFree : code.graph.CliqueFree 3) :
    code.graph.IsIndepSet (approximationOutput algorithm code) :=
  (algorithm.correctness n code triangleFree).1

theorem approximationOutput_approximation
    {ε : ℝ} (algorithm : TriangleFreeMISApproximation ε)
    {n : ℕ} (code : GraphCode n) (triangleFree : code.graph.CliqueFree 3) :
    (code.graph.indepNum : ℝ) ≤
      Real.rpow n ((1 : ℝ) / 2 - ε) *
        (approximationOutput algorithm code).card :=
  (algorithm.correctness n code triangleFree).2

/- Counted arithmetic used only by the compiled gap decision procedure. -/

def countedMul (left : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | right + 1 =>
      let prior := countedMul left right
      (prior.1 + left, prior.2 + left + 1)

def countedPow (base : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | exponent + 1 =>
      let prior := countedPow base exponent
      let product := countedMul prior.1 base
      (product.1, prior.2 + product.2 + 1)

def gapDecision (q n outputCard : ℕ) : Bool × ℕ :=
  let left := countedPow n (q + 3)
  let right := countedPow outputCard q
  (decide (left.1 ≤ right.1),
    left.2 + right.2 + left.1 + right.1 + 1)

end Lax47Proofs
