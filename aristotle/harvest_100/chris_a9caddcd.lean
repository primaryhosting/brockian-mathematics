/-
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header above is given as a plain block comment.)

import Mathlib

namespace Ordinal

/-- `ω ^ 1 = ω`.  This is the special case `a = ω` of `Ordinal.opow_one`.

Note: in current Mathlib the ordinal `ω` is called `Ordinal.omega0`
(`Ordinal.omega` is the `ω_·` order embedding), so the statement is phrased
with `omega0`. -/
theorem omega_pow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one omega0

/-- `ω ≤ ω ^ 2`, from `Ordinal.opow_le_opow_right` applied to `1 ≤ 2`. -/
theorem omega_le_omega_pow : (omega0 : Ordinal) ≤ omega0 ^ (2 : Ordinal) := by
  conv_lhs => rw [← omega_pow_one]
  exact opow_le_opow_right omega0_pos (by norm_num)

/-- The same statements phrased via the `ω_·` hierarchy, using `ω_ 0 = ω`. -/
theorem omega_zero_pow_one : (omega 0 : Ordinal) ^ (1 : Ordinal) = omega 0 :=
  opow_one _

theorem omega_zero_le_omega_zero_pow : (omega 0 : Ordinal) ≤ omega 0 ^ (2 : Ordinal) := by
  rw [omega_zero]
  exact omega_le_omega_pow

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

