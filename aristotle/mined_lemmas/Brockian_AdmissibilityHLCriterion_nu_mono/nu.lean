import Mathlib

set_option autoImplicit false

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`.
(Reproduced from the corpus module so the statement elaborates.) -/

def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- Monotonicity of the local count `ν_p` under inclusion. -/
