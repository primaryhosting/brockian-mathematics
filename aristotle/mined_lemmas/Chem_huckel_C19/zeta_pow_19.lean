/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma zeta_pow_19 : zeta ^ 19 = 1 := zeta_primitive.pow_eq_one

