import Mathlib
namespace MS.Foundations


private theorem exists_int_factorial_mul (q : ℚ) : ∃ k : ℤ, (k : ℝ) = ((q.den)! : ℝ) * (q : ℝ) := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos (le_refl q.den)
  refine ⟨(c : ℤ) * q.num, ?_⟩
  have h : ((q.den : ℝ)) * (q : ℝ) = (q.num : ℝ) := by rw [Rat.cast_def]; field_simp
  rw [hc]
  push_cast
  rw [show ((q.den : ℝ) * c * q) = c * ((q.den : ℝ) * q) by ring, h]

