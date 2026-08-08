import Lax47.Complexity
import Lax41.MoserTardosDefinitions
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Probability.ProductMeasure

/-!
---
title: Reduction certificate for triangle-free Max Independent Set
type: definition
---
This concept isolates the mathematical and running-time facts supplied by the
paper's randomized reduction. An $n$-vertex graph is sent, using a lazily read
table of independent Boolean samples, to a graph on the $n\times n$ blow-up of
its vertices. The Moser--Tardos run is stopped after a polynomial cutoff; on a
cutoff failure the output is the edgeless graph. A certificate requires that
every output is triangle-free, its independence number is always at least $n$
times that of the input, with probability at least two thirds it is at most a
constant times $\alpha(H)n\log n$, and its number of computation steps has a
uniform polynomial bound.

The formulation deliberately exposes exactly what the final promise-gap
argument consumes. The proof package constructs this certificate using the
Moser--Tardos and Haeupler--Saha--Srinivasan theorems.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax47.Reduction

open Lax41.MoserTardosDefinitions

/-- Vertices of the complete $n$-fold blow-up. -/
abbrev BlowupVertex (n : ℕ) := Fin n × Fin n

/-- Edge variables used by the resampling construction. -/
abbrev EdgeVariable (n : ℕ) := Sym2 (BlowupVertex n)

/-- The infinite table of Boolean samples read lazily by Moser--Tardos. -/
abbrev SampleTable (n : ℕ) :=
  ResamplingTable (fun _ : EdgeVariable n ↦ Bool)

/--
The probabilistic, combinatorial, and polynomial-step certificate delivered
by the reduction in the paper.
-/
structure TriangleFreeReduction where
  measure : ∀ n : ℕ, MeasureTheory.Measure (SampleTable n)
  output : ∀ (n : ℕ), SimpleGraph (Fin n) →
    SampleTable n → SimpleGraph (BlowupVertex n)
  steps : ∀ (n : ℕ), SimpleGraph (Fin n) → SampleTable n → ℕ
  probability : ∀ n, MeasureTheory.IsProbabilityMeasure (measure n)
  triangleFree : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (table : SampleTable n),
    (output n H table).CliqueFree 3
  completeness : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (table : SampleTable n),
    H.indepNum * n ≤ (output n H table).indepNum
  soundnessConstant : ℝ
  soundnessCutoff : ℕ
  soundnessConstant_pos : 0 < soundnessConstant
  soundness : ∀ (n : ℕ), soundnessCutoff ≤ n → ∀ H : SimpleGraph (Fin n),
    measure n
      {table | soundnessConstant * H.indepNum * n * Real.log n <
        ((output n H table).indepNum : ℝ)} ≤ (1 : ℝ≥0∞) / 3
  stepConstant : ℕ
  stepExponent : ℕ
  stepConstant_pos : 0 < stepConstant
  stepBound : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (table : SampleTable n),
    steps n H table ≤ stepConstant * (n + 1) ^ stepExponent

/-- Existence of a reduction certificate with the paper's parameters. -/
def HasTriangleFreeReduction : Prop :=
  Nonempty TriangleFreeReduction

end Lax47.Reduction
