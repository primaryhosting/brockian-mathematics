/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- **Integrality shadow** (Montgomery's integrality step).
For every natural number `m`, `2 * m ≤ m ^ 2 + 1`; this is the scalar shadow of
`(m - 1) ^ 2 ≥ 0`, whose matrix analogue is Lemma 3.2. -/
theorem integrality_shadow (m : Nat) : 2 * m ≤ m ^ 2 + 1 := by
  cases m with
  | zero => decide
  | succ k =>
    have h : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.mul_comm]
      omega
    rw [h]
    omega

/-- Integer form of the integrality shadow: `(m : ℤ) ^ 2 ≥ 2 * m - 1` for `m : ℕ`. -/
theorem integrality_shadow_int (m : Nat) : ((m : Int)) ^ 2 ≥ 2 * (m : Int) - 1 := by
  have h := integrality_shadow m
  have h2 : ((2 * m : Nat) : Int) ≤ ((m ^ 2 + 1 : Nat) : Int) := Int.ofNat_le.mpr h
  simp [Int.natCast_pow] at h2
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

