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

import Mathlib

/-!
# Omega Add Omega
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_add_omega
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- Ordinal arithmetic: `ω + ω = ω * 2`.

In current Mathlib the ordinal `ω` is denoted `Ordinal.omega0` (`Ordinal.omega` is the
`ω_·` indexing order embedding), so the statement is phrased with `omega0`. -/

theorem omega_add_omega : omega0 + omega0 = omega0 * 2 := by
  have h2 : (2 : Ordinal) = Order.succ 1 := by
    rw [Order.succ_eq_add_one]; norm_num
  rw [h2, mul_succ, mul_one]

/-- Restatement in terms of `Ordinal.omega 0`, which equals `ω`. -/
