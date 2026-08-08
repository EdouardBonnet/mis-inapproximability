import Lax47.Theorem12
import Lax47Proofs.GapTransfer

set_option autoImplicit false

namespace Lax47Proofs

open Lax47.Complexity Lax47.Reduction
open Lax47Proofs.GapTransfer

/--
---
conclusion: Lax47.Theorem12.theorem_1_2
---
The polynomial-cutoff randomized blow-up converts a purported
$N^{1/2-\varepsilon}$ triangle-free approximation into a bounded-error,
polynomial-step solver for Håstad's general-graph promise gap. Applying the
Håstad premise proves the triangle-free conclusion.
-/
theorem theorem_1_2 :
    Lax47.Hastad.Inapproximability →
      ∀ (ε : ℝ), 0 < ε → TriangleFreeMISApproximation ε → NPSubsetBPP := by
  intro hastad ε hε algorithm
  let δ := chosenDelta ε
  apply hastad δ
  · exact chosenDelta_pos hε
  · exact chosenDelta_lt_half ε
  · exact gapSolver Construction.reduction algorithm
      (chosenDelta_pos hε) two_mul_chosenDelta_le

end Lax47Proofs
