import Mathlib

set_option autoImplicit false

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- Subadditivity of the local count `ν_p` under unions. -/
