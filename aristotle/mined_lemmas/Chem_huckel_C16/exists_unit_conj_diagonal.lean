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

/-- A primitive 16-th root of unity. -/

lemma exists_unit_conj_diagonal :
    ∃ u : (Matrix (Fin 16) (Fin 16) ℂ)ˣ,
      ((SimpleGraph.cycleGraph 16).adjMatrix ℂ)
        = (u : Matrix (Fin 16) (Fin 16) ℂ)
            * Matrix.diagonal (fun k => ((huckelEigen k : ℝ) : ℂ))
            * (↑u⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) := by
  have hdet : IsUnit (dftMat).det := Ne.isUnit dft_det_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det dftMat).2 hdet
  refine ⟨u, ?_⟩
  have h := adj_mul_dft
  rw [← hu] at h
  calc ((SimpleGraph.cycleGraph 16).adjMatrix ℂ)
      = (C16adj * (u : Matrix (Fin 16) (Fin 16) ℂ))
          * (↑u⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) := by
        rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]; rfl
    _ = (u : Matrix (Fin 16) (Fin 16) ℂ)
          * Matrix.diagonal (fun k => ((huckelEigen k : ℝ) : ℂ))
          * (↑u⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) := by
        rw [h]

/-- **Hückel theory for the 16-annulene.**  The spectrum of the adjacency matrix of the
cycle graph `C₁₆` is exactly `{2 cos (2πk/16) : k = 0, …, 15}`. -/
