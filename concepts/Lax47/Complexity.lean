import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card

/-!
---
title: Complexity and approximation definitions for Max Independent Set
type: definition
---
This concept fixes the computational meaning of the inapproximability
statement without choosing a machine model.  A computation is accompanied by
the number of elementary steps that it takes, and polynomial time means that
this number is bounded by a fixed polynomial in the input length.  `NP` uses
polynomially long certificates checked in polynomially many steps.  `BPP`
uses polynomially many uniformly random bits, polynomially many steps, and
two-sided error at most one third.

A Max Independent Set approximation algorithm similarly supplies its output
and step count directly.  On every triangle-free `n`-vertex graph it takes
polynomially many steps, returns an independent set, and has size at least the
optimum divided by `n ^ (1 / 2 - ε)`.
-/

set_option autoImplicit false

namespace Lax47.Complexity

/-- A finite binary input or certificate. -/
abbrev BitString := List Bool

/-- A decision problem over finite binary inputs. -/
abbrev Language := Set BitString

/-- The polynomial `c (n + 1)^k`, including a harmless offset at size zero. -/
def polynomialBound (c k n : ℕ) : ℕ :=
  c * (n + 1) ^ k

/-- A family of step counts is bounded by a polynomial in the chosen size. -/
def HasPolynomialStepBound {Input : Type} (size steps : Input → ℕ) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ ∀ x, steps x ≤ polynomialBound c k (size x)

/-- A deterministic verifier with explicit certificate and step bounds. -/
structure NPVerifier (L : Language) where
  accepts : BitString → BitString → Bool
  steps : BitString → BitString → ℕ
  certificateConstant : ℕ
  certificateExponent : ℕ
  certificateConstant_pos : 0 < certificateConstant
  stepConstant : ℕ
  stepExponent : ℕ
  stepConstant_pos : 0 < stepConstant
  stepBound : ∀ x certificate,
    certificate.length ≤ polynomialBound certificateConstant certificateExponent x.length →
    steps x certificate ≤ polynomialBound stepConstant stepExponent x.length
  correctness : ∀ x : BitString,
    x ∈ L ↔ ∃ certificate : BitString,
      certificate.length ≤ polynomialBound certificateConstant certificateExponent x.length ∧
      accepts x certificate = true

/-- A language belongs to `NP` in the abstract step-count model. -/
def InNP (L : Language) : Prop :=
  Nonempty (NPVerifier L)

/-- A seed of `r` independent uniformly random bits. -/
abbrev RandomSeed (r : ℕ) := Fin r → Bool

/-- A bounded-error randomized decision algorithm with explicit step count. -/
structure BPPAlgorithm (L : Language) where
  randomnessConstant : ℕ
  randomnessExponent : ℕ
  randomnessConstant_pos : 0 < randomnessConstant
  stepConstant : ℕ
  stepExponent : ℕ
  stepConstant_pos : 0 < stepConstant
  accepts : (x : BitString) →
    RandomSeed (polynomialBound randomnessConstant randomnessExponent x.length) → Bool
  steps : (x : BitString) →
    RandomSeed (polynomialBound randomnessConstant randomnessExponent x.length) → ℕ
  stepBound : ∀ x seed,
    steps x seed ≤ polynomialBound stepConstant stepExponent x.length
  correctness : ∀ x : BitString,
    let seeds : Finset
        (RandomSeed (polynomialBound randomnessConstant randomnessExponent x.length)) :=
      Finset.univ
    let accepting := seeds.filter fun seed ↦ accepts x seed = true
    (x ∈ L → 2 * seeds.card ≤ 3 * accepting.card) ∧
      (x ∉ L → 3 * accepting.card ≤ seeds.card)

/-- A language belongs to `BPP` in the abstract step-count model. -/
def InBPP (L : Language) : Prop :=
  Nonempty (BPPAlgorithm L)

/-- The complexity-class inclusion appearing in the theorem. -/
def NPSubsetBPP : Prop :=
  ∀ L : Language, InNP L → InBPP L

/--
A polynomial-step `n^(1/2-ε)` approximation algorithm for Max Independent Set
on triangle-free graphs.
-/
structure TriangleFreeMISApproximation (ε : ℝ) where
  output : ∀ (n : ℕ), SimpleGraph (Fin n) → Finset (Fin n)
  steps : ∀ (n : ℕ), SimpleGraph (Fin n) → ℕ
  stepConstant : ℕ
  stepExponent : ℕ
  stepConstant_pos : 0 < stepConstant
  stepBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    steps n G ≤ polynomialBound stepConstant stepExponent n
  independent : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.CliqueFree 3 → G.IsIndepSet (output n G)
  approximation : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.CliqueFree 3 →
    (G.indepNum : ℝ) ≤ Real.rpow n ((1 : ℝ) / 2 - ε) * (output n G).card

end Lax47.Complexity
