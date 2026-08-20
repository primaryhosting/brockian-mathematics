import Mathlib

/-!
# Hückel theory for the cyclic polyene C₁₂

The adjacency eigenvalues of the cycle graph `C₁₂` are `2 * cos (2 * π * k / 12)` for
`k = 0, …, 11`.
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Polynomial Matrix

/-- A primitive 12-th root of unity. -/

lemma A12_charpoly :
    A12.charpoly =
      ∏ k : Fin 12, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 12) : ℝ) : ℂ)) := by
  have hu : IsUnit P12 := (Matrix.isUnit_iff_isUnit_det P12).mpr (isUnit_iff_ne_zero.mpr P12_det_ne_zero)
  obtain ⟨U, hU⟩ := hu
  have hUinv : (↑U⁻¹ : Matrix (Fin 12) (Fin 12) ℂ) = P12⁻¹ := by
    rw [Matrix.coe_units_inv, hU]
  have hA : A12 = (U : Matrix (Fin 12) (Fin 12) ℂ) * D12 * (↑U⁻¹ : Matrix (Fin 12) (Fin 12) ℂ) := by
    rw [hU, hUinv, ← A12_mul_P12, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P12 (isUnit_iff_ne_zero.mpr P12_det_ne_zero), Matrix.mul_one]
  rw [hA, Matrix.charpoly_units_conj, D12, Matrix.charpoly_diagonal]

