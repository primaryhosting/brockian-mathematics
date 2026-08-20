/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/

lemma V_isUnit : IsUnit V := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [V, Ne, Matrix.det_vandermonde_eq_zero_iff]
  rintro ⟨i, j, hij, hne⟩
  exact hne (Fin.ext (om_pow_injOn i.isLt j.isLt hij))

