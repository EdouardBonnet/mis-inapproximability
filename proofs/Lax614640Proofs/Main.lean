import Lax614640.TriangleFreeIndependentSetHardness
import Lax614640.IndependentSetGapHardness
import Lax614640Proofs.GapTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax614640Proofs

open Lax614640.Complexity
open Lax614640Proofs.GapTransfer
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime

/--
---
conclusion: Lax614640.TriangleFreeIndependentSetHardness.not_approximable
---
The polynomial-cutoff randomized blow-up converts a purported
$N^{1/2-\varepsilon}$ triangle-free approximation into a bounded-error,
polynomial-step solver for Håstad's general-graph promise gap. Håstad's
hardness theorem then contradicts $NP\nsubseteq BPP$.
-/
theorem triangleFreeMIS_not_approximable :
    ¬ NP ⊆ BPP →
      ∀ (ε : ℝ), 0 < ε → ¬ TriangleFreeMISApproximable ε := by
  rintro hcomplexity ε hε ⟨algorithm⟩
  obtain ⟨q, hq, hqε⟩ := exists_gap_parameter ε hε
  exact hcomplexity (Lax614640.IndependentSetGapHardness.gapSolver_implies_np_subset_bpp q hq
    (gapSolver q algorithm hq hqε))

end Lax614640Proofs
