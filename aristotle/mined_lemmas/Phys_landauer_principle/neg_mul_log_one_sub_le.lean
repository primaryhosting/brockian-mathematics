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

lemma neg_mul_log_one_sub_le (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    -((1 - v) * Real.log (1 - v)) ≤ v := by
  rcases eq_or_lt_of_le hv1 with h | h
  · subst h
    norm_num
  · have hu : 0 < 1 - v := by linarith
    have hkey : Real.log (1 / (1 - v)) ≤ 1 / (1 - v) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hu), Real.log_one, zero_sub] at hkey
    have hmul : (1 - v) * -Real.log (1 - v) ≤ (1 - v) * (1 / (1 - v) - 1) :=
      mul_le_mul_of_nonneg_left hkey hu.le
    have hval : (1 - v) * (1 / (1 - v) - 1) = v := by
      field_simp
      ring
    rw [hval] at hmul
    nlinarith [hmul]

/-- Binary entropy is small when the distribution is close to a point mass. -/
