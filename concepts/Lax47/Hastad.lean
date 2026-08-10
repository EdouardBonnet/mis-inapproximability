import Lax47.Gap

/-!
---
title: Håstad's inapproximability of Max Independent Set
type: definition
---
Håstad's general-graph inapproximability result supplies the hardness premise
used by the reduction.  We use its equivalent rational promise-gap form.  For
every integer $q>2$, a bounded-error polynomial-step algorithm distinguishing
$n$-vertex graphs $H$ with $\alpha(H)\leq n^{1/q}$ from those with
$n^{1-1/q}\leq\alpha(H)$ would imply $NP\subseteq BPP$.

This concept only defines that premise. It does not assert Håstad's result as
an archive axiom; the main theorem of this submission is the implication from
this premise to the triangle-free inapproximability conclusion.
-/

set_option autoImplicit false

namespace Lax47.Hastad

open Lax47.Machine Lax47.Gap

/-- Håstad's general-graph promise-gap inapproximability premise. -/
def Inapproximability : Prop :=
  ∀ q : ℕ, 3 ≤ q → MISGapSolver q → NPSubsetBPP

end Lax47.Hastad
