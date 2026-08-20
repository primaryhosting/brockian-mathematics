import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

private lemma P8_mulVec_eigvec8 :
    ((Matrix.scalar (Fin 8)) (2 - 2 * Real.cos (Real.pi / 9)) - P8).mulVec eigvec8 = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, P8, eigvec8, Matrix.scalar_apply,
      Matrix.diagonal]
  all_goals try ring_nf
  · have h := sin_three_term (Real.pi * (1 / 9))
    rw [show Real.pi * (1 / 9) - Real.pi / 9 = 0 by ring, Real.sin_zero] at h
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (2 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (3 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (4 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (5 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (6 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (7 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (8 / 9))
    rw [show Real.pi * (8 / 9) + Real.pi / 9 = Real.pi by ring, Real.sin_pi] at h
    ring_nf at h
    linarith

