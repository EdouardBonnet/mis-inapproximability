import Lax47.Complexity
import Lax41.MoserTardosDefinitions
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ProductMeasure

/-!
---
title: Reduction certificate for triangle-free Max Independent Set
type: definition
---
This concept isolates the mathematical and running-time facts supplied by the
paper's randomized reduction.  An `n`-vertex graph is sent, using an infinite
table of independent Boolean samples, to a graph on the `n × n` blow-up of its
vertices.  A certificate requires that the output is triangle-free almost
surely; its independence number is always at least `n` times that of the input;
with probability at least two thirds it is at most a constant times
`α(H) n log n`; and its expected number of resampling steps is polynomial.

The formulation deliberately exposes exactly what the Håstad--Zuckerman gap
argument consumes.  The proof package constructs this certificate using the
Moser--Tardos and Haeupler--Saha--Srinivasan theorems of Lax41.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax47.Reduction

open Lax41.MoserTardosDefinitions

/-- Vertices of the complete `n`-fold blow-up. -/
abbrev BlowupVertex (n : ℕ) := Fin n × Fin n

/-- Edge variables used by the resampling construction. -/
abbrev EdgeVariable (n : ℕ) := Sym2 (BlowupVertex n)

/-- The infinite table of Boolean samples used by Moser--Tardos. -/
abbrev SampleTable (n : ℕ) :=
  ResamplingTable (fun _ : EdgeVariable n ↦ Bool)

/--
The probabilistic, combinatorial, and expected-step certificate delivered by
the reduction in the paper.
-/
structure TriangleFreeReduction where
  measure : ∀ n : ℕ, MeasureTheory.Measure (SampleTable n)
  output : ∀ (n : ℕ), SimpleGraph (Fin n) →
    SampleTable n → SimpleGraph (BlowupVertex n)
  steps : ∀ (n : ℕ), SimpleGraph (Fin n) → SampleTable n → ℝ≥0∞
  probability : ∀ n, MeasureTheory.IsProbabilityMeasure (measure n)
  triangleFree : ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
    ∀ᵐ table ∂measure n, (output n H table).CliqueFree 3
  completeness : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (table : SampleTable n),
    H.indepNum * n ≤ (output n H table).indepNum
  soundness : ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧
    ∀ (n : ℕ), n₀ ≤ n → ∀ H : SimpleGraph (Fin n),
      (2 : ℝ≥0∞) / 3 ≤ measure n
        {table | ((output n H table).indepNum : ℝ) ≤
          C * H.indepNum * n * Real.log n}
  expectedPolynomialSteps : ∃ (C k : ℕ), 0 < C ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      ∫⁻ table, steps n H table ∂measure n ≤ (C * (n + 1) ^ k : ℕ)

/-- Existence of a reduction certificate with the paper's parameters. -/
def HasTriangleFreeReduction : Prop :=
  Nonempty TriangleFreeReduction

end Lax47.Reduction
