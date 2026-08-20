import Mathlib
namespace MS.Foundations


private theorem factorial_mul_expPartial (n : ℕ) :
    ((∑ m ∈ Finset.range (n + 1), n ! / m ! : ℕ) : ℝ) = (n ! : ℝ) * expPartial n := by
  rw [expPartial, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
  ring

/-- If `x` is rational then `q.den ! * x` is an integer. -/
