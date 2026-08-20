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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem mem_of_abs_le_abs_of_isSymmConvex {K : Set ℝ} (hK : IsSymmConvex K) {a x : ℝ}
    (ha : a ∈ K) (hx : |x| ≤ |a|) : x ∈ K := by
  obtain ⟨hconv, hsym⟩ := hK
  have hna : -a ∈ K := hsym a ha
  rcases le_total 0 a with h | h
  · have h1 : segment ℝ (-a) a ⊆ K := hconv.segment_subset hna ha
    apply h1
    rw [segment_eq_Icc (by linarith)]
    rw [abs_of_nonneg h] at hx
    exact abs_le.mp hx
  · have h1 : segment ℝ a (-a) ⊆ K := hconv.segment_subset ha hna
    apply h1
    rw [segment_eq_Icc (by linarith)]
    rw [abs_of_nonpos h] at hx
    constructor <;> [linarith [neg_abs_le x, le_abs_self x]; linarith [le_abs_self x]]

/-- Two symmetric convex subsets of `ℝ` are nested. -/
