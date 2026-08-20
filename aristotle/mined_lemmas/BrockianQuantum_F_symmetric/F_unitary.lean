import Mathlib
/-!
# Batch 11 — Fibonacci-anyon extras (F-matrix, fusion, golden identities). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
-- `Real` is opened so that `goldenRatio` refers to `Real.goldenRatio`
-- (`gold_sq` is the deprecated alias of `Real.goldenRatio_sq`).
open Matrix Real

theorem F_unitary : Fmat * Fmatᴴ = 1 := by
  have hs : Real.sqrt goldenRatio⁻¹ ^ 2 = goldenRatio⁻¹ := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fmat, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.one_apply_eq,
      Fin.mk_zero, Fin.mk_one] <;>
    first
      | nlinarith [golden_inv_sq_add, hs]
      | (rw [Matrix.one_apply_ne (by decide)]; ring)

