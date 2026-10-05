/-
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Scalar core of the Nyman–Beurling finite-shape distance identity: if the squared
projection length `p ^ 2` does not exceed the squared norm `u ^ 2` of a vector
(with `0 ≤ u`), then the residual squared distance `u ^ 2 - p ^ 2` is nonnegative. -/

theorem finite_distance_sq_eq_one_sub_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [FiniteDimensional ℝ K] (x : E)
    (hx : ‖x‖ = 1) :
    (⨅ y : K, ‖x - y‖) ^ 2 = 1 - ‖K.starProjection x‖ ^ 2 ∧
      0 ≤ 1 - ‖K.starProjection x‖ ^ 2 ∧ 1 - ‖K.starProjection x‖ ^ 2 ≤ 1 := by
  have hsplit : ‖x‖ ^ 2 = ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2 := by
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x K
    have h2 : x - K.starProjection x = Kᗮ.starProjection x :=
      (Submodule.starProjection_orthogonal_val x).symm
    rw [h2, h]
  have hmin : (⨅ y : K, ‖x - y‖) = ‖x - K.starProjection x‖ :=
    (Submodule.starProjection_minimal x).symm
  rw [hx] at hsplit
  refine ⟨?_, ?_, ?_⟩
  · rw [hmin]; nlinarith [hsplit]
  · nlinarith [sq_nonneg ‖x - K.starProjection x‖]
  · nlinarith [sq_nonneg ‖K.starProjection x‖]

end NymanBeurling

