import Lax405409.Theorem12
import Lax405409Proofs.GapTransfer

set_option autoImplicit false

namespace Lax405409Proofs

open Lax405409.Complexity
open Lax405409Proofs.GapTransfer

/--
---
conclusion: Lax405409.Theorem12.theorem_1_2
---
The polynomial-cutoff randomized blow-up converts a purported
$N^{1/2-\varepsilon}$ triangle-free approximation into a bounded-error,
polynomial-step solver for Håstad's general-graph promise gap. Applying the
Håstad premise proves the triangle-free conclusion.
-/
theorem theorem_1_2 :
    Lax405409.Hastad.Inapproximability →
      ∀ (ε : ℝ), 0 < ε → TriangleFreeMISApproximation ε → NPSubsetBPP := by
  intro hastad ε hε algorithm
  obtain ⟨q, hq, hqε⟩ := exists_gap_parameter ε hε
  exact hastad q hq (gapSolver q algorithm hq hqε)

end Lax405409Proofs
