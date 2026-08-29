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

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem om_primitive : IsPrimitiveRoot om 18 := by
  have h := Complex.isPrimitiveRoot_exp 18 (by norm_num)
  simpa [om] using h

