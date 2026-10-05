import Mathlib
/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- `ω ^ 1 = ω`. -/
theorem omega_pow_one : (ω : Ordinal) ^ (1 : Ordinal) = ω := by
  simp

/-- `ω ≤ ω ^ 2`. -/
theorem omega_le_omega_pow : (ω : Ordinal) ≤ (ω : Ordinal) ^ (2 : Ordinal) := by
  calc (ω : Ordinal) = (ω : Ordinal) ^ (1 : Ordinal) := omega_pow_one.symm
    _ ≤ (ω : Ordinal) ^ (2 : Ordinal) := opow_le_opow_right omega0_pos (by norm_num)

end Ordinal

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

