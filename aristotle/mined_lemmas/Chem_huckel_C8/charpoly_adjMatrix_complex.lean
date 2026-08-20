import Mathlib

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

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma charpoly_adjMatrix_complex :
    ((SimpleGraph.cycleGraph 8).adjMatrix ℂ).charpoly =
      ∏ k : Fin 8, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) : ℂ)) := by
  have hunit : IsUnit Pv.det := isUnit_iff_ne_zero.2 Pv_det_ne_zero
  have hconj : (SimpleGraph.cycleGraph 8).adjMatrix ℂ =
      ((Matrix.nonsingInvUnit Pv hunit : (Matrix (Fin 8) (Fin 8) ℂ)ˣ) : Matrix (Fin 8) (Fin 8) ℂ) *
        Dg * ((Matrix.nonsingInvUnit Pv hunit)⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ) := by
    show _ = Pv * Dg * Pv⁻¹
    rw [← adjMatrix_mul_Pv, Matrix.mul_assoc, Matrix.mul_nonsing_inv Pv hunit, Matrix.mul_one]
  rw [hconj, Matrix.charpoly_units_conj, Dg, Matrix.charpoly_diagonal]

