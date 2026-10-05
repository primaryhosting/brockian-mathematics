/-!
# Nu Union Le
Category: Brockian External
Target: Brockian.AdmissibilityHLCriterion.nu_union_le
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- Subadditivity of the local count `ν_p` under unions. -/
theorem nu_union_le (p : ℕ) (S T : Finset ℤ) :
    nu p (S ∪ T) ≤ nu p S + nu p T := by
  unfold nu residueImage
  rw [Finset.image_union]
  exact Finset.card_union_le _ _

end Brockian.AdmissibilityHLCriterion

