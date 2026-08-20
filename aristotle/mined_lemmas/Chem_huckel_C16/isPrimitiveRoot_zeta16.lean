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

lemma isPrimitiveRoot_zeta16 : IsPrimitiveRoot zeta16 16 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  norm_num at h
  simpa [zeta16] using h

