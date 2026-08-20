import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

lemma lapl_sq_coord (x : E3) : lapl (fun y : E3 => (y 0) * (y 0)) x = 2 := by
  have hproj : ∀ v : E3, (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ) v = v 0 := fun _ => rfl
  have hp : ∀ y : E3, HasFDerivAt (fun z : E3 => (z 0) * (z 0))
      ((y 0) • (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)
        + (y 0) • (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)) y := by
    intro y
    have h0 : HasFDerivAt (fun z : E3 => z 0) (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ) y :=
      (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt
    simpa [add_comm, smul_eq_mul] using h0.mul h0
  have h1 : ∀ (i : Fin 3) (y : E3), partialD i (fun z : E3 => (z 0) * (z 0)) y
      = 2 * (y 0) * (EuclideanSpace.single i (1 : ℝ) 0) := by
    intro i y
    simp only [partialD, (hp y).fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, hproj, smul_eq_mul]
    ring
  have h2 : ∀ i : Fin 3, partialD i (fun y : E3 => partialD i (fun z : E3 => (z 0) * (z 0)) y) x
      = 2 * (EuclideanSpace.single i (1 : ℝ) 0) * (EuclideanSpace.single i (1 : ℝ) 0) := by
    intro i
    have he : (fun y : E3 => partialD i (fun z : E3 => (z 0) * (z 0)) y)
        = fun y : E3 => (2 * (EuclideanSpace.single i (1 : ℝ) 0)) * (y 0) := by
      funext y; rw [h1 i y]; ring
    rw [he]
    have h0 : HasFDerivAt (fun y : E3 => (2 * (EuclideanSpace.single i (1 : ℝ) 0)) * (y 0))
        ((2 * (EuclideanSpace.single i (1 : ℝ) 0))
          • (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)) x :=
      ((EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt).const_mul _
    simp only [partialD, h0.fderiv, ContinuousLinearMap.smul_apply, hproj, smul_eq_mul]
  simp [lapl, h2, EuclideanSpace.single_apply]

/-! ## The base case : the zero solution -/

/-- The zero velocity field with zero pressure is a global smooth solution. -/
