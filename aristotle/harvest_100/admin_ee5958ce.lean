/-
# Omega Add Omega
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_add_omega
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Ordinal

/-- **Omega add omega**: `ω + ω = ω * 2` in ordinal arithmetic.

In current Mathlib the ordinal `ω` is named `Ordinal.omega0` (the name `Ordinal.omega`
now refers to the order embedding indexing initial ordinals), so the statement is
phrased with `Ordinal.omega0`.

The proof writes `2 = Order.succ 1` and uses `Ordinal.mul_succ : a * Order.succ b = a * b + a`.
Note that the generic `mul_two` is unavailable here, since ordinal multiplication is only
left-distributive over addition. -/
theorem omega_add_omega : Ordinal.omega0 + Ordinal.omega0 = Ordinal.omega0 * 2 := by
  have h2 : (2 : Ordinal) = Order.succ (1 : Ordinal) := by simp
  rw [h2, Ordinal.mul_succ, mul_one]

end Ordinal

