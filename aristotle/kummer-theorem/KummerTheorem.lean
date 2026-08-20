import Mathlib
namespace Brockian.KummerTheorem
/-- Kummer's theorem (digit-sum form): for a prime p, the p-adic valuation of C(m+n, m),
    times (p−1), equals S_p(m) + S_p(n) − S_p(m+n), where S_p is the base-p digit sum
    (equivalently, the number of carries when adding m and n in base p). -/
theorem kummer (p m n : ℕ) (hp : p.Prime) :
    (Nat.choose (m + n) m).factorization p * (p - 1) =
      (Nat.digits p m).sum + (Nat.digits p n).sum - (Nat.digits p (m + n)).sum := by
  sorry
end Brockian.KummerTheorem
