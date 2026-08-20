import Mathlib
/-!
# Batch 11 — Fibonacci-anyon extras (F-matrix, fusion, golden identities). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
-- `Real` is opened so that `goldenRatio` refers to `Real.goldenRatio`
-- (`gold_sq` is the deprecated alias of `Real.goldenRatio_sq`).
open Matrix Real

theorem F_det : Fmat.det = -1 := by
  have hs : Real.sqrt goldenRatio⁻¹ ^ 2 = goldenRatio⁻¹ := Real.sq_sqrt (by positivity)
  rw [Matrix.det_fin_two]
  simp only [Fmat, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  nlinarith [golden_inv_sq_add, hs]

