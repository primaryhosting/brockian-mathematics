import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma logsum_pointwise {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 < A) (hB : 0 < B) (hac : b = 0 → a = 0) :
    a - b * (A / B) ≤ a * Real.log (a / b) - a * Real.log (A / B) := by
  rcases eq_or_lt_of_le ha with h | ha'
  · have ha0 : a = 0 := h.symm
    subst ha0
    have : 0 ≤ b * (A / B) := by positivity
    simpa using this
  · have hb' : 0 < b := by
      rcases eq_or_lt_of_le hb with h | h
      · exact absurd (hac h.symm) (ne_of_gt ha')
      · exact h
    set x : ℝ := (a * B) / (b * A) with hx
    have hxpos : 0 < x := by rw [hx]; positivity
    have hlog : 1 - 1 / x ≤ Real.log x := by
      have h1 : Real.log (1 / x) ≤ 1 / x - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (1 / x) = - Real.log x := by
        rw [one_div, Real.log_inv]
      rw [h2] at h1
      linarith
    have e1 : Real.log (a / b) = Real.log a - Real.log b := Real.log_div ha'.ne' hb'.ne'
    have e2 : Real.log (A / B) = Real.log A - Real.log B := Real.log_div hA.ne' hB.ne'
    have e3 : Real.log x = Real.log (a * B) - Real.log (b * A) := by
      rw [hx]
      exact Real.log_div (mul_ne_zero ha'.ne' hB.ne') (mul_ne_zero hb'.ne' hA.ne')
    have e4 : Real.log (a * B) = Real.log a + Real.log B := Real.log_mul ha'.ne' hB.ne'
    have e5 : Real.log (b * A) = Real.log b + Real.log A := Real.log_mul hb'.ne' hA.ne'
    have hxeq : Real.log (a / b) - Real.log (A / B) = Real.log x := by
      rw [e1, e2, e3, e4, e5]; ring
    have hstep : a * (1 - 1 / x) ≤ a * Real.log x :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt ha')
    have hinv : a * (1 / x) = b * (A / B) := by
      rw [hx, one_div, inv_div]
      field_simp
    have hgoal : a * Real.log (a / b) - a * Real.log (A / B) = a * Real.log x := by
      rw [← hxeq]; ring
    rw [hgoal]
    nlinarith [hstep, hinv]

/-- **Log-sum inequality**: `(∑ a) log ((∑ a)/(∑ b)) ≤ ∑ a log (a/b)`. -/
