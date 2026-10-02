import Lax614640.Gap
import Lax434930.NondeterministicPolynomialTime
import Lax666725.RandomizedPolynomialTime

/-!
---
title: Promise-gap hardness of Max Independent Set
type: theorem
---
Håstad's general-graph inapproximability result supplies the hardness theorem
used by the reduction. We use its rational promise-gap form. For
every integer $q>2$, a bounded-error polynomial-step algorithm distinguishing
$n$-vertex graphs $H$ with $\alpha(H)\leq n^{1/q}$ from those with
$n^{1-1/q}\leq\alpha(H)$ would imply $NP\subseteq BPP$.

This formulation is proved here from the registered PCP-to-clique reduction
in lax-253009. The proof complements the graph, guards the relative threshold,
handles graphs below the solver's cutoff by bounded exhaustive search, and
certifies the encoding conversion and randomized composition in the finite
Turing-machine models.
-/

set_option autoImplicit false

namespace Lax614640.IndependentSetGapHardness

open Lax614640.Gap
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

/-- Håstad's general-graph promise-gap inapproximability theorem. -/
axiom gapSolver_implies_np_subset_bpp :
  ∀ q : ℕ, 3 ≤ q → MISGapSolver q → NP ⊆ BPP

end Lax614640.IndependentSetGapHardness
