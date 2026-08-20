import Mathlib
namespace Brockian.Zsygmondy
/-- Zsygmondy's theorem (Bang's case b=1, n ≥ 3): aⁿ − 1 has a primitive prime divisor —
    a prime dividing aⁿ − 1 but no aᵐ − 1 for 0 < m < n — except for (a,n) = (2,6). -/
theorem zsygmondy_primitive_prime (a n : ℕ) (ha : 2 ≤ a) (hn : 3 ≤ n)
    (hexc : ¬ (a = 2 ∧ n = 6)) :
    ∃ p, p.Prime ∧ p ∣ (a ^ n - 1) ∧ ∀ m, 0 < m → m < n → ¬ p ∣ (a ^ m - 1) := by
  sorry
end Brockian.Zsygmondy
