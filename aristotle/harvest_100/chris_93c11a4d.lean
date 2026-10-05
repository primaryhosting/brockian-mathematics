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
# Integrality Three Halves
Category: Riemann Program
Target: Riemann.Method.integrality_three_halves
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- Auxiliary step: every natural number is at most its own square. -/
private theorem self_le_mul_self (k : Nat) : k ≤ k * k := by
  cases k with
  | zero => exact Nat.le_refl 0
  | succ j => exact Nat.le_mul_of_pos_left (j + 1) (Nat.succ_pos j)

/-- **Integrality three halves.** For every natural number `m` we have `3 * m ≤ m ^ 2 + 2`,
i.e. `m ^ 2 ≥ 3 * m - 2`, which is the integer form of `(m - 1) * (m - 2) ≥ 0`. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  cases m with
  | zero => decide
  | succ k =>
    obtain ⟨c, hc⟩ := Nat.le.dest (self_le_mul_self k)
    have hpow : (k + 1) ^ 2 = k * k + 2 * k + 1 := by
      simp [Nat.pow_succ, Nat.mul_add, Nat.mul_comm]
      omega
    rw [hpow, ← hc]
    omega

end Riemann.Method

