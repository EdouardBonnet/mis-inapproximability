import Lax47.Complexity
import Lax47.Reduction

/-!
---
title: Håstad--Zuckerman hardness of Max Independent Set
type: theorem
---
For every constant `δ ∈ (0, 1/2)`, it is NP-hard to distinguish an
`n`-vertex graph with independence number at most `n^δ` from one with
independence number at least `n^(1-δ)` (the promise version of Zuckerman's
Theorem 1.1 on graph complements, strengthening Håstad's result).

Here the promise theorem is stated in the transfer form used by the paper: if
the randomized expected-polynomial-step triangle-free blow-up reduction has been
certified, then any polynomial-time `N^(1/2-ε)` approximation algorithm for
triangle-free Max Independent Set yields a bounded-error randomized
polynomial-time algorithm for the hard gap problem, and hence `NP ⊆ BPP`.
The elementary choice `δ = 2ε`, cutoff, amplification, and finite exceptional
inputs are included in this standard promise-hardness transfer so that the
only unproved concept is precisely the Håstad--Zuckerman complexity result.
-/

set_option autoImplicit false

namespace Lax47.HastadZuckerman

open Lax47.Complexity Lax47.Reduction

/-- Håstad--Zuckerman promise hardness, in the reduction-transfer form. -/
axiom gap_hardness_transfer :
  HasTriangleFreeReduction →
  ∀ (ε : ℝ), 0 < ε → TriangleFreeMISApproximation ε → NPSubsetBPP

end Lax47.HastadZuckerman
