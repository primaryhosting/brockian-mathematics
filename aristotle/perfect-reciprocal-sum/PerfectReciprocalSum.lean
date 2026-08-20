import Mathlib
namespace Brockian.PerfectReciprocalSum
/-- The sum of the reciprocals of the divisors of a perfect number equals 2
    (since σ(n) = 2n). -/
theorem perfect_reciprocal_sum (n : ℕ) (hn : 0 < n) (hp : Nat.Perfect n) :
    ∑ d ∈ n.divisors, (1 / (d : ℚ)) = 2 := by
  sorry
end Brockian.PerfectReciprocalSum
