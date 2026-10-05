/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment; it is repeated as a module
-- docstring immediately after the imports.)

import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

/-- The `±1` phase attached to a boolean value: `sgn b = (-1)^b`. -/

lemma abs_djAmp_of_isConstant {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsConstant f) :
    |djAmp f| = 1 := by
  classical
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rcases Bool.eq_false_or_eq_true (f (fun _ => false)) with hc | hc
  · have hfilter : (Finset.univ.filter fun x : Fin n → Bool => f x = true) = Finset.univ := by
      apply Finset.filter_eq_self.2
      intro x _
      simp [hf x (fun _ => false), hc]
    have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by
      simp
    rw [djAmp_eq, sum_sgn, hfilter, hcard]
    rw [show (2 : ℝ) ^ n - 2 * 2 ^ n = -(2 ^ n) by ring]
    rw [neg_div, div_self (ne_of_gt hpos), abs_neg, abs_one]
  · have hfilter : (Finset.univ.filter fun x : Fin n → Bool => f x = true) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro x _
      simp [hf x (fun _ => false), hc]
    rw [djAmp_eq, sum_sgn, hfilter]
    simp

/-- A balanced function produces the all-zeros outcome with probability zero:
the amplitude vanishes. -/
