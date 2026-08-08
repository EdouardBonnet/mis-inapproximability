import Lax47.Complexity

/-!
---
title: Tight inapproximability of Max Independent Set in triangle-free graphs
type: theorem
---
For every constant `ε > 0`, there is no polynomial-time
`N^(1/2-ε)`-approximation algorithm for Max Independent Set on `N`-vertex
triangle-free graphs unless `NP ⊆ BPP`.

Equivalently, and in the implication form formalized below, the existence of
such an approximation algorithm implies `NP ⊆ BPP`.  This is the main
triangle-free inapproximability theorem (Theorem 1 in the supplied proceedings
version, referred to as Theorem 1.2 in the submission request).
-/

set_option autoImplicit false

namespace Lax47.Theorem12

open Lax47.Complexity

/-- Tight conditional inapproximability of MIS on triangle-free graphs. -/
axiom theorem_1_2 :
  ∀ (ε : ℝ), 0 < ε → TriangleFreeMISApproximation ε → NPSubsetBPP

end Lax47.Theorem12
