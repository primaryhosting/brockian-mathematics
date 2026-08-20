import Mathlib
open Matrix Polynomial
namespace C5.BSp6

lemma mulVec_eq_zero :
    ((Matrix.scalar (Fin 10) (2 - 2 * Real.cos (Real.pi / 11))) - P10) *ᵥ v10 = 0 := by
  have k0 := sin_three_term 0
  have k1 := sin_three_term 1
  have k2 := sin_three_term 2
  have k3 := sin_three_term 3
  have k4 := sin_three_term 4
  have k5 := sin_three_term 5
  have k6 := sin_three_term 6
  have k7 := sin_three_term 7
  have k8 := sin_three_term 8
  have k9 := sin_three_term 9
  have h11 := sin_eleven
  norm_num [Real.sin_zero] at k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
  rw [h11] at k9
  funext i
  fin_cases i <;>
  · simp only [Matrix.mulVec, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      dotProduct, P10, Matrix.of_apply, v10, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.zero_apply,
      Fin.val_succ, Fin.ext_iff, Fin.val_zero]
    norm_num
    linarith

