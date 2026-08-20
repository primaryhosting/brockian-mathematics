import Mathlib
namespace Brockian.MsJacobiTwo
/-- Jacobi's two-square theorem: the number of ways to write n > 0 as an ordered sum of two
    integer squares equals 4·(d₁(n) − d₃(n)), where d_i counts divisors ≡ i (mod 4). -/
theorem jacobi_two_square (n : ℕ) (hn : 0 < n) :
    (Finset.filter (fun v : ℤ × ℤ => v.1 ^ 2 + v.2 ^ 2 = n)
        (Finset.Icc (-(n:ℤ)) n ×ˢ Finset.Icc (-(n:ℤ)) n)).card
      = 4 * (((n.divisors.filter (fun d => d % 4 = 1)).card : ℤ)
           - ((n.divisors.filter (fun d => d % 4 = 3)).card)) := by
  sorry
end Brockian.MsJacobiTwo
