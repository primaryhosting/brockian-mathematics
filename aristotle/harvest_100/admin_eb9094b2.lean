/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- **Simple Zero Shadow.**

For every natural number `m` with `1 ≤ m` we have `2 * m ≤ m ^ 2 + 1`, and equality
holds exactly when `m = 1`.  Equivalently `m ^ 2 + 1 - 2 * m = (m - 1) ^ 2 ≥ 0`, the
integrality step used to separate *simple* zeros in Montgomery's two-thirds argument. -/
theorem simple_zero_shadow (m : Nat) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hsq : (k + 1) ^ 2 = k * k + (2 * k + 1) := by
    simp [Nat.pow_succ, Nat.succ_mul, Nat.mul_succ]
    omega
  rw [hsq]
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    have hk : k * k = 0 := by omega
    have hk0 : k = 0 := by
      rcases Nat.mul_eq_zero.mp hk with h0 | h0 <;> exact h0
    omega
  · intro h
    have hk0 : k = 0 := by omega
    subst hk0
    omega

end Riemann.Method

#print axioms Riemann.Method.simple_zero_shadow

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

