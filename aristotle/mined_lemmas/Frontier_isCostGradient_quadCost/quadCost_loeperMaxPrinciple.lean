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

theorem quadCost_loeperMaxPrinciple :
    LoeperMaxPrinciple (E := E) quadCost (fun x y => x - y) := by
  intro x x₀ y hseg t ht
  have hy : y t = (1 - t) • y 0 + t • y 1 := by
    have h := hseg t
    simp only at h
    have h2 : (1 - t) • (x₀ - y 0) + t • (x₀ - y 1) = x₀ - ((1 - t) • y 0 + t • y 1) := by
      module
    rw [h2] at h
    exact sub_right_injective h
  -- the function `z ↦ c x₀ z - c x z` is affine in `z`
  have hval : ∀ z : E, quadCost x₀ z - quadCost x z
      = (‖x₀‖ ^ 2 - ‖x‖ ^ 2) / 2 - inner ℝ (x₀ - x) z := by
    intro z
    simp only [quadCost, norm_sub_sq_real, inner_sub_left]
    ring
  rw [hval (y t), hval (y 0), hval (y 1), hy]
  have hlin : inner ℝ (x₀ - x) ((1 - t) • y 0 + t • y 1)
      = (1 - t) * inner ℝ (x₀ - x) (y 0) + t * inner ℝ (x₀ - x) (y 1) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hlin]
  have := affine_le_max (a := (‖x₀‖ ^ 2 - ‖x‖ ^ 2) / 2 - inner ℝ (x₀ - x) (y 0))
    (b := (‖x₀‖ ^ 2 - ‖x‖ ^ 2) / 2 - inner ℝ (x₀ - x) (y 1)) ht.1 ht.2
  linarith

end MTW

/-! ### One-dimensional regularity of optimal maps -/

/-- Two-point (`c`-cyclical) monotonicity for the quadratic cost forces monotonicity of the
transport map on the line. -/
