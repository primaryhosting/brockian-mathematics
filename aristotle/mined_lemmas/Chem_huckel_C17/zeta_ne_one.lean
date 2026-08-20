/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma zeta_ne_one : zeta ≠ 1 := by
  simpa using zeta_primitive.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num)

/-- The standard additive character of `ZMod 17`, `x ↦ exp (2πi x / 17)`. -/
