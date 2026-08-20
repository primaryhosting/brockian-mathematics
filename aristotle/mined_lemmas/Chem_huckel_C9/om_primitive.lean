import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem om_primitive : IsPrimitiveRoot om 9 := by
  simpa [om, mul_comm, mul_assoc, mul_left_comm] using Complex.isPrimitiveRoot_exp 9 (by norm_num)

