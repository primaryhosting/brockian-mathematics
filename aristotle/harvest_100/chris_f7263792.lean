/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- Montgomery's integrality step, natural-number form: since `(m - 1) ^ 2 ≥ 0`,
we have `2 * m ≤ m ^ 2 + 1` for every `m : Nat`. -/
theorem integrality_shadow (m : Nat) : 2 * m ≤ m ^ 2 + 1 := by
  have hsq : m ^ 2 = m * m := by
    rw [Nat.pow_succ, Nat.pow_one]
  rw [hsq]
  cases m with
  | zero => decide
  | succ k =>
    have e1 : (k + 1) * (k + 1) = (k * k + k) + (k + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    rw [e1]
    generalize k * k = a
    omega

/-- Integer form of the integrality shadow: `(m : Int) ^ 2 ≥ 2 * m - 1`. -/
theorem integrality_shadow_int (m : Nat) : ((m : Int)) ^ 2 ≥ 2 * (m : Int) - 1 := by
  have h : 2 * m ≤ m ^ 2 + 1 := integrality_shadow m
  have hc : ((m : Int)) ^ 2 = ((m ^ 2 : Nat) : Int) := by
    rw [Int.natCast_pow]
  rw [hc]
  generalize m ^ 2 = s at h ⊢
  omega

end Zeta23Redux.LinAlg

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

