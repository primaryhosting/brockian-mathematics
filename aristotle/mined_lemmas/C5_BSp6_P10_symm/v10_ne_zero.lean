import Mathlib
open Matrix Polynomial
namespace C5.BSp6

lemma v10_ne_zero : v10 ≠ 0 := by
  intro h
  have h0 : v10 0 = 0 := by rw [h]; rfl
  simp only [v10] at h0
  norm_num at h0
  have hpos : 0 < Real.sin (Real.pi / 11) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [Real.pi_pos]
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- `v10` lies in the kernel of `(2 - 2 cos (π/11)) • I - P10`. -/
