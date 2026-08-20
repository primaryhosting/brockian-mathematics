import Mathlib
/-!
# Batch 11 — Fibonacci-anyon extras (F-matrix, fusion, golden identities). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
-- `Real` is opened so that `goldenRatio` refers to `Real.goldenRatio`
-- (`gold_sq` is the deprecated alias of `Real.goldenRatio_sq`).
open Matrix Real

noncomputable def Fmat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![goldenRatio⁻¹, Real.sqrt goldenRatio⁻¹; Real.sqrt goldenRatio⁻¹, -goldenRatio⁻¹]
/-- Fibonacci fusion matrix N_τ. -/

theorem F_symmetric : Fmatᵀ = Fmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
