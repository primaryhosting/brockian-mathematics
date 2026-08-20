import Mathlib
namespace MS.Foundations


theorem irrational_e : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  set n := q.den
  have hn1 : 1 ≤ n := q.pos
  obtain ⟨k, hk⟩ := exists_int_factorial_mul q
  rw [hq] at hk
  refine absurd (expTail_lt_one n hn1) (not_lt.mpr ?_)
  set M : ℤ := k - (∑ m ∈ Finset.range (n + 1), n ! / m ! : ℕ) with hM
  have hMR : (M : ℝ) = (n ! : ℝ) * (Real.exp 1 - expPartial n) := by
    rw [hM, Int.cast_sub, Int.cast_natCast, factorial_mul_expPartial n, mul_sub, ← hk]
  have hMpos : 0 < M := by
    have := expTail_pos n
    rw [← hMR] at this
    exact_mod_cast this
  have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
  rw [hMR] at this
  exact this

end ExpIrrational

