import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

open MeasureTheory

namespace Frontier

/-- Auxiliary: a differentiable function is continuous. -/

private lemma exists_base_point {u : ℝ → ℝ} (hsupp : HasCompactSupport u) (x : ℝ) :
    ∃ a : ℝ, a ≤ x ∧ u a = 0 := by
  obtain ⟨R, hR0, hR⟩ := hsupp.exists_pos_le_norm
  refine ⟨min x (-R), min_le_left _ _, hR _ ?_⟩
  have h : min x (-R) ≤ -R := min_le_right _ _
  have hneg : min x (-R) < 0 := lt_of_le_of_lt h (by linarith)
  rw [Real.norm_eq_abs, abs_of_neg hneg]
  linarith

/-- **Gagliardo–Nirenberg–Sobolev, one-dimensional base case (`L¹` form).**
If `u : ℝ → ℝ` is differentiable with derivative `u'` and has compact support, and `u'` is
integrable, then `u` is bounded by the `L¹` norm of its derivative. -/
