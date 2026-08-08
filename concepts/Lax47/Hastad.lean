import Lax47.Complexity

/-!
---
title: Håstad's inapproximability of Max Independent Set
type: definition
---
Håstad's general-graph inapproximability result supplies the hardness premise
used by the reduction. In promise-gap form, for every constant
$\delta\in(0,1/2)$, a bounded-error polynomial-step algorithm distinguishing
$n$-vertex graphs $H$ with $\alpha(H)\leq n^\delta$ from those with
$\alpha(H)\geq n^{1-\delta}$ would imply $NP\subseteq BPP$.

This concept only defines that premise. It does not assert Håstad's result as
an archive axiom; the main theorem of this submission is the implication from
this premise to the triangle-free inapproximability conclusion.
-/

set_option autoImplicit false

namespace Lax47.Hastad

open Lax47.Complexity

/-- Håstad's general-graph promise-gap inapproximability premise. -/
def Inapproximability : Prop :=
  ∀ (δ : ℝ), 0 < δ → δ < (1 : ℝ) / 2 →
    MISGapSolver δ → NPSubsetBPP

end Lax47.Hastad
