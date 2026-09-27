import Lax47.Gap
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

This result is assumed without proof.
-/

set_option autoImplicit false

namespace Lax47.IndependentSetGapHardness

open Lax47.Gap
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

/-- Håstad's general-graph promise-gap inapproximability theorem. -/
axiom gapSolver_implies_np_subset_bpp :
  ∀ q : ℕ, 3 ≤ q → MISGapSolver q → NP ⊆ BPP

end Lax47.IndependentSetGapHardness
