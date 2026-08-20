import Mathlib
/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the header comment above appears just after `import Mathlib`.

namespace Ordinal

/-- `ω ^ 1 = ω`, an instance of the Mathlib lemma `Ordinal.opow_one`. -/
theorem omega_pow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`.  This follows from monotonicity of ordinal exponentiation in the
exponent (`Ordinal.opow_le_opow_right`, which needs `0 < ω`, i.e. `Ordinal.omega0_pos`)
together with `ω ^ 1 = ω` (`Ordinal.opow_one`).

Note: in current Mathlib the ordinal `ω` is called `Ordinal.omega0`
(`Ordinal.omega` denotes the `ω_` indexing function on ordinals). -/
theorem omega_le_omega_pow : (omega0 : Ordinal) ≤ omega0 ^ (2 : Ordinal) := by
  calc (omega0 : Ordinal) = omega0 ^ (1 : Ordinal) := omega_pow_one.symm
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

