import Lax47.Complexity

/-!
---
title: Håstad--Zuckerman hardness of Max Independent Set
type: theorem
---
For every constant $\delta\in(0,1/2)$, it is $NP$-hard to distinguish an
$n$-vertex graph $H$ with $\alpha(H)\le n^\delta$ from one with
$\alpha(H)\ge n^{1-\delta}$. This is the promise version of Zuckerman's
Theorem 1.1 on graph complements, strengthening Håstad's result.

The Lean statement records precisely the computational consequence of that
promise hardness: a bounded-error polynomial-step solver for the
general-graph promise gap implies $NP\subseteq BPP$. It contains no
triangle-free reduction and no conclusion from the present paper.
-/

set_option autoImplicit false

namespace Lax47.HastadZuckerman

open Lax47.Complexity

/-- The general-graph promise-hardness implication. -/
def GapHardnessStatement : Prop :=
  ∀ (δ : ℝ), 0 < δ → δ < (1 : ℝ) / 2 →
    MISGapSolver δ → NPSubsetBPP

/-- Håstad--Zuckerman promise hardness for general Max Independent Set. -/
axiom gap_hardness : GapHardnessStatement

end Lax47.HastadZuckerman
