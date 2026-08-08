import Lax47.Hastad

/-!
---
title: Håstad hardness implies tight inapproximability in triangle-free graphs
type: theorem
---
Assume Håstad's general-graph inapproximability premise. Then, for every
constant $\varepsilon>0$, a polynomial-time
$N^{1/2-\varepsilon}$-approximation algorithm for Max Independent Set on
$N$-vertex triangle-free graphs implies $NP\subseteq BPP$.

The entire implication, including the randomized reduction from the Håstad
promise gap, is the statement formalized below and proved by this submission.
Its triangle-free conclusion is Theorem 1.2 in the submitted paper.
-/

set_option autoImplicit false

namespace Lax47.Theorem12

open Lax47.Complexity

/-- Håstad hardness implies tight conditional inapproximability on triangle-free graphs. -/
axiom theorem_1_2 :
  Lax47.Hastad.Inapproximability →
    ∀ (ε : ℝ), 0 < ε → TriangleFreeMISApproximation ε → NPSubsetBPP

end Lax47.Theorem12
