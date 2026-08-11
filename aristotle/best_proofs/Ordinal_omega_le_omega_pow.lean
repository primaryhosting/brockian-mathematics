/-
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`
-- because Lean 4 requires `import` commands to precede any command, including docstrings.)

import Mathlib

/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- `ω ^ 1 = ω`, where `ω = Ordinal.omega0` is the first infinite ordinal.

(In current Mathlib the first infinite ordinal is named `Ordinal.omega0`; the name
`Ordinal.omega` denotes the order embedding `ω_ : Ordinal ↪o Ordinal`.) -/
theorem omega_pow_one : omega0 ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`, where `ω = Ordinal.omega0` is the first infinite ordinal. -/
theorem omega_le_omega_pow : omega0 ≤ omega0 ^ (2 : Ordinal) := by
  calc omega0 = omega0 ^ (1 : Ordinal) := omega_pow_one.symm
    _ ≤ omega0 ^ (2 : Ordinal) := opow_le_opow_right omega0_pos (by norm_num)

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

