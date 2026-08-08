import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
---
title: Complexity and approximation definitions for Max Independent Set
type: definition
---
This concept fixes the computational meaning of the inapproximability
statement without choosing a machine model. A computation is accompanied by
the number of elementary steps that it takes, and polynomial time means that
this number is bounded by a fixed polynomial in the input length. The class
$NP$ uses polynomially long certificates checked in polynomially many steps.
The class $BPP$ uses polynomially many uniformly random bits, polynomially
many steps, and two-sided error at most one third.

A Max Independent Set approximation algorithm similarly supplies its output
and step count. On every triangle-free graph with $N$ vertices it takes
polynomially many steps, returns an independent set, and has size at least the
optimum divided by $N^{1/2-\varepsilon}$.

The general-graph promise-gap solver used to state Håstad's premise may use a
bundled probability space. It must run in polynomially many steps and, for all
sufficiently large $n$, distinguish
$\alpha(H)\ge n^{1-\delta}$ from $\alpha(H)\le n^\delta$ with error at most
one third.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax47.Complexity

/-- A finite binary input or certificate. -/
abbrev BitString := List Bool

/-- A decision problem over finite binary inputs. -/
abbrev Language := Set BitString

/-- The polynomial $c(n+1)^k$, including a harmless offset at size zero. -/
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

/-- A language belongs to $NP$ in the abstract step-count model. -/
def InNP (L : Language) : Prop :=
  Nonempty (NPVerifier L)

/-- A seed of $r$ independent uniformly random bits. -/
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

/-- A language belongs to $BPP$ in the abstract step-count model. -/
def InBPP (L : Language) : Prop :=
  Nonempty (BPPAlgorithm L)

/-- The complexity-class inclusion appearing in the theorem. -/
def NPSubsetBPP : Prop :=
  ∀ L : Language, InNP L → InBPP L

/-- A probability space bundled so that a randomized graph algorithm may choose its sample type. -/
structure ProbabilitySpace where
  Sample : Type
  measurableSpace : MeasurableSpace Sample
  measure : @MeasureTheory.Measure Sample measurableSpace
  probability : @MeasureTheory.IsProbabilityMeasure Sample measurableSpace measure

instance (P : ProbabilitySpace) : MeasurableSpace P.Sample :=
  P.measurableSpace

instance (P : ProbabilitySpace) : MeasureTheory.IsProbabilityMeasure P.measure :=
  P.probability

/-- A polynomial-step approximation algorithm for triangle-free Max Independent Set. -/
structure TriangleFreeMISApproximation (ε : ℝ) where
  output : ∀ (V : Type) [Fintype V] [DecidableEq V], SimpleGraph V → Finset V
  steps : ∀ (V : Type) [Fintype V] [DecidableEq V], SimpleGraph V → ℕ
  stepConstant : ℕ
  stepExponent : ℕ
  stepConstant_pos : 0 < stepConstant
  stepBound : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    steps V G ≤ polynomialBound stepConstant stepExponent (Fintype.card V)
  independent : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.CliqueFree 3 → G.IsIndepSet (output V G)
  approximation : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.CliqueFree 3 →
    (G.indepNum : ℝ) ≤
      Real.rpow (Fintype.card V) ((1 : ℝ) / 2 - ε) * (output V G).card

/--
A bounded-error polynomial-step solver for Håstad's promise gap.
Correctness is required only beyond a fixed cutoff, which is equivalent for
hardness purposes because the finitely many smaller graphs can be handled
exactly.
-/
structure MISGapSolver (δ : ℝ) where
  sampleSpace : ℕ → ProbabilitySpace
  accepts : (n : ℕ) → SimpleGraph (Fin n) → (sampleSpace n).Sample → Prop
  steps : (n : ℕ) → SimpleGraph (Fin n) → (sampleSpace n).Sample → ℕ
  stepConstant : ℕ
  stepExponent : ℕ
  stepConstant_pos : 0 < stepConstant
  stepBound : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (sample : (sampleSpace n).Sample),
    steps n H sample ≤ polynomialBound stepConstant stepExponent n
  cutoff : ℕ
  completeness : ∀ (n : ℕ), cutoff ≤ n → ∀ H : SimpleGraph (Fin n),
    Real.rpow n (1 - δ) ≤ H.indepNum →
      (2 : ℝ≥0∞) / 3 ≤ (sampleSpace n).measure {sample | accepts n H sample}
  soundness : ∀ (n : ℕ), cutoff ≤ n → ∀ H : SimpleGraph (Fin n),
    (H.indepNum : ℝ) ≤ Real.rpow n δ →
      (sampleSpace n).measure {sample | accepts n H sample} ≤ (1 : ℝ≥0∞) / 3

end Lax47.Complexity
