import Lax614640.IndependentSetGapHardness
import Lax614640Proofs.GapTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax614640Proofs.IndependentSetGapHardness

open Lax614640.Machine Lax614640.Complexity Lax614640.Gap
open Lax434930.NondeterministicPolynomialTime
open Lax666725.RandomizedPolynomialTime
open Lax253009Proofs Lax253009Proofs.RegisteredBridge
open PCPFoundation.Complexity (algBase one_lt_algBase_deg)
open RandomizedApproximationTest BoundedErrorTests

/--
---
conclusion: Lax614640.IndependentSetGapHardness.gapSolver_implies_np_subset_bpp
---
Apply the registered PCP-to-clique gap reduction with exponent $1/q$.
The threshold guard converts its relative gap into the absolute independent-set
gap on the complement. Graphs below the solver cutoff are handled by bounded
exhaustive search. The finite-Turing adapter certifies this comparison, and
independent majority trials provide the error bound needed for composition.
-/
theorem gapSolver_implies_np_subset_bpp :
    ∀ q : ℕ, 3 ≤ q → MISGapSolver q → NP ⊆ BPP := by
  intro q hq solver
  have hqpos : 0 < q := by omega
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  intro L hL
  obtain ⟨R⟩ := clique_gap_reduction algBase one_lt_algBase_deg ((q : ℝ)⁻¹)
    (inv_pos.mpr hqreal) (inv_le_one_of_one_le₀ hqone) L hL
  apply compose_in_BPP R (GapTest.test solver).boost
  · intro x coins
    simp [Test.boost_bits, context_pair, GapTest.test]
  · intro x hx coins
    rw [context_pair]
    apply Test.boost_error
    exact GapTest.complete_error solver (R.graph x coins) (R.threshold x)
      (R.nonempty x) hqpos (R.complete x hx coins)
  · intro x coins hh
    rw [context_pair]
    apply Test.boost_error
    exact GapTest.sound_error solver (R.graph x coins) (R.threshold x)
      hqpos (Nat.lt_of_not_ge hh)

end Lax614640Proofs.IndependentSetGapHardness
