import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

private lemma eigvec8_ne_zero : eigvec8 ≠ 0 := by
  intro h
  have h0 : eigvec8 0 = 0 := by rw [h]; rfl
  have hpos : 0 < Real.sin (Real.pi / 9) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith [Real.pi_pos])
  simp only [eigvec8] at h0
  norm_num at h0
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

