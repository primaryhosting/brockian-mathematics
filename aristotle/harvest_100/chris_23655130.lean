import Mathlib

/-!
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
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

namespace NymanBeurling

/-- **Nyman–Beurling finite shape, scalar core.**

In a real inner product space, the squared distance from a unit vector `u` to a
finite-dimensional subspace equals `‖u‖^2 - ‖p‖^2`, where `p` is the orthogonal
projection; since `‖p‖ ≤ ‖u‖`, this residual is nonnegative.

This is the self-contained scalar statement: for reals `u`, `p` with `p^2 ≤ u^2`
and `0 ≤ u`, the residual `u^2 - p^2` is nonnegative.

The hypothesis `0 ≤ u` is included because it is part of the requested statement
(the norm of a vector is nonnegative), but it is not needed for the conclusion. -/
theorem finite_distance_nonneg (u p : ℝ) (hu : 0 ≤ u) (hp : p ^ 2 ≤ u ^ 2) :
    0 ≤ u ^ 2 - p ^ 2 := by
  rcases le_or_gt 0 (u ^ 2 - p ^ 2) with h | h
  · exact h
  · exact absurd (by linarith : u ^ 2 < p ^ 2) (not_lt.mpr hp)

/-- The vector-level statement behind the scalar core: for a unit vector `x` and a
subspace `K` admitting an orthogonal projection (e.g. a finite-dimensional subspace),
the squared distance from `x` to `K` is `1 - ‖P_K x‖ ^ 2`. -/
theorem sq_dist_unit_eq_one_sub_sq_norm_proj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E)
    (hx : ‖x‖ = 1) :
    ‖x - K.starProjection x‖ ^ 2 = 1 - ‖K.starProjection x‖ ^ 2 := by
  have h := K.norm_sq_eq_add_norm_sq_starProjection x
  rw [hx] at h
  have hx' : x - K.starProjection x = Kᗮ.starProjection x := by simp
  rw [one_pow] at h
  rw [hx']
  linarith

/-- The squared distance from a unit vector to such a subspace lies in `[0, 1]`. -/
theorem sq_dist_unit_mem_Icc {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E)
    (hx : ‖x‖ = 1) :
    ‖x - K.starProjection x‖ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  rw [sq_dist_unit_eq_one_sub_sq_norm_proj K x hx]
  have : (0 : ℝ) ≤ ‖K.starProjection x‖ ^ 2 := sq_nonneg _
  linarith

end NymanBeurling

