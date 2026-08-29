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

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/

lemma isPrimitiveRoot_zeta17 : IsPrimitiveRoot zeta17 17 :=
  Complex.isPrimitiveRoot_exp 17 (by norm_num)

