import Lax47.HastadZuckerman
import Lax47.Theorem12
import Lax47Proofs.GapTransfer

set_option autoImplicit false

namespace Lax47Proofs

open Lax47.Complexity Lax47.Reduction
open Lax47Proofs.GapTransfer

/--
---
conclusion: Lax47.Theorem12.theorem_1_2
assumptions:
  - Lax47.HastadZuckerman.gap_hardness
---
The polynomial-cutoff randomized blow-up converts a purported
$N^{1/2-\varepsilon}$ triangle-free approximation into a bounded-error,
polynomial-step solver for the Håstad--Zuckerman general-graph promise gap.
-/
theorem theorem_1_2 :
    ∀ (ε : ℝ), 0 < ε → TriangleFreeMISApproximation ε → NPSubsetBPP := by
  intro ε hε algorithm
  let δ := chosenDelta ε
  apply Lax47.HastadZuckerman.gap_hardness δ
  · exact chosenDelta_pos hε
  · exact chosenDelta_lt_half ε
  · exact gapSolver Construction.reduction algorithm
      (chosenDelta_pos hε) two_mul_chosenDelta_le

end Lax47Proofs
