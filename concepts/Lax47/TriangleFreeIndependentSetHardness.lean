import Lax47.Complexity
import Lax434930.NondeterministicPolynomialTime
import Lax666725.RandomizedPolynomialTime

/-!
---
title: Tight inapproximability of Max Independent Set in triangle-free graphs
type: theorem
---
Unless $NP\subseteq BPP$, for every constant $\varepsilon>0$, Max
Independent Set on $N$-vertex triangle-free graphs admits no polynomial-time
$N^{1/2-\varepsilon}$-approximation algorithm.

This is Theorem 1.2. Its proof uses Håstad's general-graph promise-gap
hardness theorem and a randomized triangle-removal reduction.
-/

set_option autoImplicit false

namespace Lax47.TriangleFreeIndependentSetHardness

open Lax47.Complexity
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

/-- Unless $NP\subseteq BPP$, no polynomial-time $N^{1/2-\varepsilon}$
approximation exists for Max Independent Set on triangle-free graphs. -/
axiom not_approximable :
  ¬ NP ⊆ BPP →
    ∀ (ε : ℝ), 0 < ε → ¬ TriangleFreeMISApproximable ε

end Lax47.TriangleFreeIndependentSetHardness
