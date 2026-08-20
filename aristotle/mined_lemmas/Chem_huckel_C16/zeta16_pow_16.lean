/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma zeta16_pow_16 : zeta16 ^ 16 = 1 := isPrimitiveRoot_zeta16.pow_eq_one

