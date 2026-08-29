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

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- `iter f t g` is the `t`-fold iterate `f^[t] g`. -/

theorem two_pow_succ_mul (t u : Nat) : 2 ^ (t + 1) * u = 2 * (2 ^ t * u) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ t) 2, Nat.mul_assoc]

section Dinur

variable {G : Type u}

/-- **Amplification.**  If one step of Dinur's transformation at least doubles the
unsat value (until the target value `gap` is reached), then `t` steps multiply it by
`2 ^ t` (until `gap` is reached). -/
