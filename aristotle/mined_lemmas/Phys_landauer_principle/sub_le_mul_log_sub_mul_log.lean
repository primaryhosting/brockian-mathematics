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

lemma sub_le_mul_log_sub_mul_log (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : b = 0 → a = 0) : a - b ≤ a * Real.log a - a * Real.log b := by
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha0 : a = 0 := h hb0.symm
    simp [ha0, ← hb0]
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · simp [← ha0]
      linarith
    · have key : Real.log (b / a) ≤ b / a - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hb0) (ne_of_gt ha0)] at key
      have h2 : a * (Real.log b - Real.log a) ≤ a * (b / a - 1) :=
        mul_le_mul_of_nonneg_left key ha
      have h3 : a * (b / a - 1) = b - a := by
        field_simp
      rw [h3] at h2
      nlinarith [h2]

/-- Gibbs' inequality / nonnegativity of the relative entropy, in the general form
where `f` has total mass at least that of `g`. -/
