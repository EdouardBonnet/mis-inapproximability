import Lax47.Reduction

/-!
---
title: Operational promise-gap algorithms for Max Independent Set
type: definition
---
The Håstad premise is stated for executable promise-gap programs.  A program
is either a binary Turing program or the fixed triangle-removal pipeline used
in this submission.  The latter constructor is transparent: it runs the
finite-bit reduction, invokes the supplied Turing approximation program on
the encoded output graph, and compares two natural powers using the counted
unary arithmetic below.

Thus acceptance, random-bit use, and running time are functions of the same
execution.  There is no semantic answer function and no unrelated step
annotation.  For an integer $q>2$, the high promise is
$n^{1-1/q}\leq\alpha(H)$, the low promise is
$\alpha(H)\leq n^{1/q}$, and the acceptance threshold is
$n^{q+3}\leq |S|^q$.
-/

set_option autoImplicit false

namespace Lax47.Gap

open Lax47.Machine Lax47.Complexity Lax47.Reduction

/-- Length of the fixed unary-size adjacency-matrix graph encoding. -/
def graphEncodingLength (n : ℕ) : ℕ :=
  n + 1 + n * n

/- ### Counted unary arithmetic used by the acceptance test -/

/-- Unary multiplication paired with the work performed by its recursion. -/
def countedMul (left : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | right + 1 =>
      let prior := countedMul left right
      (prior.1 + left, prior.2 + left + 1)

/-- Unary exponentiation paired with the work performed by its recursion. -/
def countedPow (base : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | exponent + 1 =>
      let prior := countedPow base exponent
      let product := countedMul prior.1 base
      (product.1, prior.2 + product.2 + 1)

/-- The concrete threshold comparison and its unary-operation count. -/
def gapDecision (q n outputCard : ℕ) : Bool × ℕ :=
  let left := countedPow n (q + 3)
  let right := countedPow outputCard q
  (decide (left.1 ≤ right.1),
    left.2 + right.2 + left.1 + right.1 + 1)

/- ### Closed operational programs -/

/--
Codes accepted by the promise-gap model.  The second constructor is a fixed
composition primitive whose evaluator is defined below.
-/
inductive GapProgram (q : ℕ) where
  | machine (program : PolytimeProgram)
      (randomnessConstant randomnessExponent : ℕ)
  | triangleReduction (ε : ℝ) (algorithm : TriangleFreeMISApproximation ε)

/-- Finite uniform seed type read by a gap program on an $n$-vertex graph. -/
def GapProgram.Seed {q : ℕ} : GapProgram q → ℕ → Type
  | .machine _ constant exponent, n =>
      RandomSeed (polynomialBound constant exponent (graphEncodingLength n))
  | .triangleReduction _ _, n => ExecutionSeed n

instance {q : ℕ} (program : GapProgram q) (n : ℕ) :
    Fintype (program.Seed n) := by
  cases program <;> simp only [GapProgram.Seed] <;> infer_instance

instance {q : ℕ} (program : GapProgram q) (n : ℕ) :
    DecidableEq (program.Seed n) := by
  cases program <;> simp only [GapProgram.Seed] <;> infer_instance

instance {q : ℕ} (program : GapProgram q) (n : ℕ) :
    Nonempty (program.Seed n) := by
  cases program <;> simp only [GapProgram.Seed] <;> infer_instance

/-- Number of independent fair bits in the structured seed. -/
def GapProgram.randomBitCount {q : ℕ} : GapProgram q → ℕ → ℕ
  | .machine _ constant exponent, n =>
      polynomialBound constant exponent (graphEncodingLength n)
  | .triangleReduction _ _, n =>
      Fintype.card (EdgeVariable n) * (executionBudget n + 1) *
        executionSampleBits n

/-- List representation of a machine-constructor seed. -/
def machineSeedBits {r : ℕ} (seed : RandomSeed r) : BitString :=
  List.ofFn seed

/-- Boolean answer returned by the operational program. -/
def GapProgram.accepts {q : ℕ} :
    (program : GapProgram q) → (n : ℕ) → GraphCode n →
      program.Seed n → Bool
  | .machine program _ _, _, input, seed =>
      decide (program.output
        (pairBits input.bits (machineSeedBits seed)) = [true])
  | .triangleReduction _ algorithm, n, input, seed =>
      (gapDecision q n
        (algorithm.output (executionOutput input seed)).card).1

/-- Work charged to the same evaluation that returns $GapProgram.accepts$. -/
def GapProgram.steps {q : ℕ} :
    (program : GapProgram q) → (n : ℕ) → GraphCode n →
      program.Seed n → ℕ
  | .machine program _ _, _, input, seed =>
      polynomialBound program.timeConstant program.timeExponent
        (pairBits input.bits (machineSeedBits seed)).length
  | .triangleReduction _ algorithm, n, input, seed =>
      let reduced := executionOutput input seed
      let output := algorithm.output reduced
      executionSteps input seed +
        polynomialBound algorithm.program.timeConstant
          algorithm.program.timeExponent reduced.bits.length +
        (n * n + 1) ^ 2 +
        (gapDecision q n output.card).2

/-- Uniform seed enumeration for an operational program. -/
def GapProgram.seeds {q : ℕ} (program : GapProgram q) (n : ℕ) :
    Finset (program.Seed n) :=
  Finset.univ

/-- Seeds on which the operational program returns true. -/
def GapProgram.acceptingSeeds {q : ℕ} (program : GapProgram q)
    (n : ℕ) (input : GraphCode n) : Finset (program.Seed n) :=
  (program.seeds n).filter fun seed ↦ program.accepts n input seed

/- ### Certified polynomial gap solvers -/

/--
A bounded-error polynomial-time solver for Håstad's rational promise gap.
All resource functions are fixed by $GapProgram$; this structure supplies only
their polynomial bounds and the two correctness proofs.
-/
structure MISGapSolver (q : ℕ) where
  program : GapProgram q
  timeConstant : ℕ
  timeExponent : ℕ
  timeConstant_pos : 0 < timeConstant
  timeBound : ∀ (n : ℕ) (input : GraphCode n) (seed : program.Seed n),
    program.steps n input seed ≤ polynomialBound timeConstant timeExponent n
  randomnessConstant : ℕ
  randomnessExponent : ℕ
  randomnessConstant_pos : 0 < randomnessConstant
  randomnessBound : ∀ n : ℕ, program.randomBitCount n ≤
    polynomialBound randomnessConstant randomnessExponent n
  cutoff : ℕ
  completeness : ∀ (n : ℕ), cutoff ≤ n → ∀ input : GraphCode n,
    Real.rpow n (1 - (q : ℝ)⁻¹) ≤ (input.graph.indepNum : ℝ) →
      2 * (program.seeds n).card ≤
        3 * (program.acceptingSeeds n input).card
  soundness : ∀ (n : ℕ), cutoff ≤ n → ∀ input : GraphCode n,
    (input.graph.indepNum : ℝ) ≤ Real.rpow n ((q : ℝ)⁻¹) →
      3 * (program.acceptingSeeds n input).card ≤
        (program.seeds n).card

end Lax47.Gap
