/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace
open Matrix

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

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `psi`:
the norm of `A psi` after subtracting its mean value `⟪psi, A psi⟫ • psi`. -/

theorem heisenberg_uncertainty_sharp :
    ∃ (X P : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (psi : EuclideanSpace ℂ (Fin 2)) (hbar : ℝ),
      0 < hbar ∧ IsSymmetricOp X ∧ IsSymmetricOp P ∧ ‖psi‖ = 1 ∧
        X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi ∧
        spread X psi * spread P psi = hbar / 2 := by
  refine ⟨pauliXOp, pauliYOp, state0, 2, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp [pauliXOp, PiLp.inner_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      RCLike.inner_apply]
    ring
  · intro u v
    simp [pauliYOp, PiLp.inner_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      RCLike.inner_apply]
    ring
  · simp [state0, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  · ext i
    fin_cases i
    · simp [pauliXOp, pauliYOp, state0, dotProduct, Fin.sum_univ_two]
      ring
    · simp [pauliXOp, pauliYOp, state0, dotProduct, Fin.sum_univ_two]
  · have hX0 : ⟪state0, pauliXOp state0⟫_ℂ = 0 := by
      simp [pauliXOp, state0, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    have hP0 : ⟪state0, pauliYOp state0⟫_ℂ = 0 := by
      simp [pauliYOp, state0, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    have hXs : spread pauliXOp state0 = 1 := by
      rw [spread, hX0]
      simp [pauliXOp, state0, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have hPs : spread pauliYOp state0 = 1 := by
      rw [spread, hP0]
      simp [pauliYOp, state0, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [hXs, hPs]
    norm_num

end QPhys

