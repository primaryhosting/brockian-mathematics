import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/

lemma omega9_primitive : IsPrimitiveRoot omega9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)

