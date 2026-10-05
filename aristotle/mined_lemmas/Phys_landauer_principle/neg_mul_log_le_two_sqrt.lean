import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

lemma neg_mul_log_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) :
    -(x * Real.log x) ≤ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h]
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 h
    have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx]; ring
    have hkey : Real.log (1 / Real.sqrt x) ≤ 1 / Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hs), Real.log_one, zero_sub] at hkey
    have hmul : x * -Real.log (Real.sqrt x) ≤ x * (1 / Real.sqrt x - 1) :=
      mul_le_mul_of_nonneg_left hkey hx
    have hdiv : x * (1 / Real.sqrt x - 1) = Real.sqrt x - x := by
      have : x * (1 / Real.sqrt x) = x / Real.sqrt x := by ring
      rw [mul_sub, this, Real.div_sqrt, mul_one]
    rw [hdiv] at hmul
    rw [hlog]
    nlinarith [hmul, hx]

