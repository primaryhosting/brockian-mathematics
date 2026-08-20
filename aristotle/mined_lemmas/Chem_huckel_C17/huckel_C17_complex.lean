import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Polynomial Matrix SimpleGraph

/-- A primitive 17-th root of unity. -/

theorem huckel_C17_complex :
    ((cycleGraph 17).adjMatrix ℂ).charpoly
      = ∏ k : Fin 17, (X - C ((lam k : ℝ) : ℂ)) := by
  have hunit : IsUnit Fmat := (Matrix.isUnit_iff_isUnit_det Fmat).2 (Ne.isUnit Fmat_det_ne_zero)
  set u := hunit.unit with hu
  have hA : ((cycleGraph 17).adjMatrix ℂ)
      = u.val * Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ)) * (u⁻¹ : (Matrix (Fin 17) (Fin 17) ℂ)ˣ).val := by
    have hval : (u : Matrix (Fin 17) (Fin 17) ℂ) = Fmat := hunit.unit_spec
    rw [hval, Matrix.coe_units_inv, ← hunit.unit_spec, hval, ← adjMatrix_mul_Fmat,
      Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit Fmat_det_ne_zero)]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

