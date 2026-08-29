import Mathlib

set_option autoImplicit false

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`.
(Reproduced from the corpus module so the statement elaborates.) -/

def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
