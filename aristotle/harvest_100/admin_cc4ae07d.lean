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

For a unit vector `u` (norm `u`) and the norm `p` of its orthogonal projection onto a
finite-dimensional subspace, the squared residual distance is `u ^ 2 - p ^ 2`.  Since
`p ^ 2 ≤ u ^ 2` (Bessel's inequality), this residual is nonnegative.

The hypothesis `0 ≤ u` is part of the requested statement (it records that `u` is a norm);
it is not needed for the conclusion. -/
theorem finite_distance_nonneg (u p : ℝ) (hp : p ^ 2 ≤ u ^ 2) (_hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 :=
  sub_nonneg.mpr hp

/-- **Nyman–Beurling finite shape (vector form).**

In a real inner product space, for a unit vector `x` and a finite-dimensional subspace `K`,
the squared distance from `x` to `K` equals `1` minus the squared norm of the orthogonal
projection of `x` onto `K`, and that squared projection norm lies in `[0, 1]`. -/
theorem finite_distance_sq_eq_one_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [FiniteDimensional ℝ K] (x : E) (hx : ‖x‖ = 1) :
    (⨅ v : K, ‖x - (v : E)‖) ^ 2 = 1 - ‖K.starProjection x‖ ^ 2 ∧
      ‖K.starProjection x‖ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have key := Submodule.norm_sq_eq_add_norm_sq_projection x K
  rw [hx] at key
  have h1 : ‖Kᗮ.orthogonalProjection x‖ = ‖x - K.starProjection x‖ := by
    rw [Submodule.orthogonalProjection_orthogonal]; rfl
  have h2 : ‖K.orthogonalProjection x‖ = ‖K.starProjection x‖ := rfl
  rw [h1, h2] at key
  have hmin : ‖x - K.starProjection x‖ = ⨅ v : K, ‖x - (v : E)‖ :=
    Submodule.starProjection_minimal x
  refine ⟨by rw [← hmin]; nlinarith [key], by positivity, ?_⟩
  nlinarith [sq_nonneg ‖x - K.starProjection x‖]

end NymanBeurling

