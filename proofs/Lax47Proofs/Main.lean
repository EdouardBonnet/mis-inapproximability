import Lax47.Theorem12
import Lax47.Hastad
import Lax47Proofs.GapTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax47Proofs

open Lax47.Complexity
open Lax47Proofs.GapTransfer
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

/--
---
conclusion: Lax47.Theorem12.theorem_1_2
---
The polynomial-cutoff randomized blow-up converts a purported
$N^{1/2-\varepsilon}$ triangle-free approximation into a bounded-error,
polynomial-step solver for Håstad's general-graph promise gap. Håstad's
hardness theorem then contradicts $NP\nsubseteq BPP$.
-/
theorem theorem_1_2 :
    ¬ NP ⊆ BPP →
      ∀ (ε : ℝ), 0 < ε → ¬ TriangleFreeMISApproximable ε := by
  rintro hcomplexity ε hε ⟨algorithm⟩
  obtain ⟨q, hq, hqε⟩ := exists_gap_parameter ε hε
  exact hcomplexity (Lax47.Hastad.inapproximability q hq
    (gapSolver q algorithm hq hqε))

end Lax47Proofs
