/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- **Simple zero shadow.**  For every natural number `m` with `1 ≤ m` we have
`2 * m ≤ m ^ 2 + 1`, with equality if and only if `m = 1`.

This is Montgomery's integrality step `(m - 1) ^ 2 ≥ 0`, which separates *simple* zeros
in the two-thirds argument. -/
theorem simple_zero_shadow (m : Nat) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- Expand `(k + 1) ^ 2 + 1 = k * k + 2 * (k + 1)`; the slack is exactly the square `k * k`.
  have h : (k + 1) ^ 2 + 1 = k * k + 2 * (k + 1) := by
    simp [Nat.pow_succ, Nat.pow_zero, Nat.succ_mul, Nat.mul_succ]
    omega
  rw [h]
  refine ⟨by omega, ⟨fun hh => ?_, fun hh => ?_⟩⟩
  · -- Equality forces `k * k = 0`, hence `k = 0`, i.e. `m = 1`.
    rcases k with _ | j
    · rfl
    · exfalso
      have h0 : (j + 1) * (j + 1) = 0 := by omega
      simp [Nat.succ_mul, Nat.mul_succ] at h0
  · -- Conversely `m = 1` gives `2 = 2`.
    have hk : k = 0 := by omega
    subst hk
    simp

end Riemann.Method

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

