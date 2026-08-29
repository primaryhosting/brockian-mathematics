import Mathlib

/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to come first in a file, so the header
module docstring above is placed immediately after the single `import Mathlib`
line rather than at the very top of the file.
-/

namespace Ordinal

/-- `ω ^ 1 = ω`.

Note on naming: in current Mathlib the ordinal `ω` is `Ordinal.omega0` (the name
`Ordinal.omega` now denotes the order embedding `ω_ : Ordinal ↪o Ordinal` enumerating
the infinite initial ordinals), so the statement is phrased with `Ordinal.omega0`. -/
theorem omega_pow_one : omega0 ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`. -/
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

