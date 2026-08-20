import Mathlib
/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem symmConvex_subset_total {K L : Set ℝ} (hK : IsSymmConvex K) (hL : IsSymmConvex L) :
    K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h1
  obtain ⟨y, hyL, hyK⟩ := Set.not_subset.mp h2
  rcases le_total |y| |x| with h | h
  · exact hyK (hK.mem_of_abs_le hxK h)
  · exact hxL (hL.mem_of_abs_le hyL h)

/-- **Base case of the Gaussian correlation inequality (dimension one).**
In fact any probability measure on `ℝ` satisfies the correlation inequality for
symmetric convex sets, since these are totally ordered by inclusion. -/
