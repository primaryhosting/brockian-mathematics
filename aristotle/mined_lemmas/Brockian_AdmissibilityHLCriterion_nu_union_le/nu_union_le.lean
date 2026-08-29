import Mathlib

set_option autoImplicit false

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

theorem nu_union_le (p : ℕ) (S T : Finset ℤ) :
    nu p (S ∪ T) ≤ nu p S + nu p T := by
  unfold nu residueImage
  rw [Finset.image_union]
  exact Finset.card_union_le _ _

end Brockian.AdmissibilityHLCriterion

