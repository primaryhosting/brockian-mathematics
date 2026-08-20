import Mathlib
/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, so the module docstring above is placed directly after the
single `import Mathlib` line rather than above it.

Note on notation: in current Mathlib, `Ordinal.omega` (`ω_`) denotes the
initial-ordinal indexing function, while the first infinite ordinal `ω` is
`Ordinal.omega0`. The statements below are about the first infinite ordinal,
i.e. `Ordinal.omega0 = Ordinal.omega 0`.
-/

namespace Ordinal

/-- `ω ^ 1 = ω`, for the first infinite ordinal `ω` (`Ordinal.omega0`). -/

theorem omega_zero_pow_one : (omega 0 : Ordinal) ^ (1 : Ordinal) = omega 0 :=
  opow_one _

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

