import Mathlib
/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-! ### The Ma–Trudinger–Wang condition (Loeper's form) -/

section MTW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem monotone_of_quadCost_cyclMonotone {T : ℝ → ℝ}
    (hopt : ∀ x y : ℝ,
      quadCost x (T x) + quadCost y (T y) ≤ quadCost x (T y) + quadCost y (T x)) :
    Monotone T := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  by_contra hcon
  push_neg at hcon
  have h := hopt x y
  simp only [quadCost, Real.norm_eq_abs, sq_abs] at h
  nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hcon)]

/-- An upper density bound gives an upper bound for the measure of an interval. -/
