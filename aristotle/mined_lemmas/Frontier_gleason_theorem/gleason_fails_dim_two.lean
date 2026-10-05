import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *frame function of weight one*, Gleason's formulation of a quantum measure:
a function on the unit sphere which is nonnegative and whose values sum to `1`
over every orthonormal basis. -/
structure IsFrameFunction (f : H → ℝ) : Prop where
  nonneg : ∀ x : H, ‖x‖ = 1 → 0 ≤ f x
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H, ∑ i, f (b i) = 1

/-- A density operator: a positive (hence self-adjoint) operator of trace one. -/

theorem gleason_fails_dim_two :
    ∃ f : C2 → ℝ, IsFrameFunction f ∧
      ¬ ∃ T : C2 →L[ℂ] C2, IsDensityOperator T ∧
        ∀ x : C2, ‖x‖ = 1 → f x = RCLike.re ⟪T x, x⟫_ℂ := by
  refine ⟨qfTwo, isFrameFunction_qfTwo, ?_⟩
  rintro ⟨T, hT, hrep⟩
  refine not_quadratic_qfTwo ⟨T, fun x hx => ?_⟩
  have hre := ((ContinuousLinearMap.isPositive_iff_complex T).mp hT.1 x).1
  rw [hrep x hx, hre]

end DimTwo

/-- The density operator representing a quantum measure is unique. -/
