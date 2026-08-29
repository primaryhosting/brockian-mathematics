/-
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- `ω ^ 1 = ω`, where `ω = Ordinal.omega0` is the first infinite ordinal. -/
theorem omega0_opow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one omega0

/-- `ω ≤ ω ^ 2`, where `ω = Ordinal.omega0` is the first infinite ordinal. -/
theorem omega_le_omega_pow : (omega0 : Ordinal) ≤ omega0 ^ (2 : Ordinal) := by
  conv_lhs => rw [← omega0_opow_one]
  exact opow_le_opow_right omega0_pos one_le_two

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

