import Lax47.HastadZuckerman
import Lax47.Theorem12
import Lax47Proofs.Construction

set_option autoImplicit false

namespace Lax47Proofs

open Lax47.Complexity Lax47.Reduction

/--
---
conclusion: Lax47.Theorem12.theorem_1_2
assumptions:
  - Lax47.HastadZuckerman.gap_hardness_transfer
---
The randomized blow-up construction is certified using the kernel-checked
Moser--Tardos and Haeupler--Saha--Srinivasan theorems.  The
Håstad--Zuckerman promise-gap transfer then turns any purported
`N^(1/2-ε)` approximation into `NP ⊆ BPP`.
-/
theorem theorem_1_2 :
    ∀ (ε : ℝ), 0 < ε → TriangleFreeMISApproximation ε → NPSubsetBPP := by
  intro ε hε algorithm
  apply Lax47.HastadZuckerman.gap_hardness_transfer
  · exact ⟨Construction.reduction⟩
  · exact hε
  · exact algorithm

end Lax47Proofs
