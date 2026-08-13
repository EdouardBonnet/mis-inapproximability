import Lax47.Complexity

/-!
---
title: Finite-Turing promise-gap algorithms for Max Independent Set
type: definition
---
The Håstad premise is stated only for functions certified by Lax51's genuine
finite-Turing polynomial-time predicate.  A randomized program fixes constants
$c,k$ and receives exactly $c(n+1)^k$ uniform bits on an $n$-vertex input.
There is no special constructor for the reduction and no detached step
annotation.  For an integer $q>2$, the high promise is
$n^{1-1/q}\leq\alpha(H)$, the low promise is
$\alpha(H)\leq n^{1/q}$, and the acceptance threshold is
$n^{q+3}\leq |S|^q$.
-/

set_option autoImplicit false

namespace Lax47.Gap

open Lax47.Machine Lax47.Complexity

/- ### Standard randomized finite-Turing programs -/

/-- A polynomial-time finite-Turing program with one fixed monomial tape bound. -/
structure GapProgram (q : ℕ) where
  program : PolytimeProgram
  randomnessConstant : ℕ
  randomnessExponent : ℕ
  randomnessConstant_pos : 0 < randomnessConstant

/-- The exact, uniformly specified random-tape length on order $n$. -/
def GapProgram.randomBitCount {q : ℕ} (program : GapProgram q) (n : ℕ) : ℕ :=
  polynomialBound program.randomnessConstant program.randomnessExponent n

/-- Finite uniform seed type read by a gap program on an $n$-vertex graph. -/
abbrev GapProgram.Seed {q : ℕ} (program : GapProgram q) (n : ℕ) :=
  RandomSeed (program.randomBitCount n)

/-- Boolean answer returned by the program's certified Turing computation. -/
def GapProgram.accepts {q : ℕ} (program : GapProgram q) (n : ℕ)
    (input : GraphCode n) (seed : program.Seed n) : Bool :=
  decide (program.program.output (pairBits input.bits seed.bits) = [1])

/-- Uniform seed enumeration for a finite-Turing program. -/
def GapProgram.seeds {q : ℕ} (program : GapProgram q) (n : ℕ) :
    Finset (program.Seed n) :=
  Finset.univ

/-- Seeds on which the finite-Turing program returns true. -/
def GapProgram.acceptingSeeds {q : ℕ} (program : GapProgram q)
    (n : ℕ) (input : GraphCode n) : Finset (program.Seed n) :=
  (program.seeds n).filter fun seed ↦ program.accepts n input seed

/- ### Certified polynomial gap solvers -/

/--
A bounded-error finite-Turing polynomial-time solver for Håstad's rational
promise gap. The uniform random-tape length is the fixed monomial stored in
the gap program.
-/
structure MISGapSolver (q : ℕ) where
  program : GapProgram q
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
