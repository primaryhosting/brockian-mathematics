import Mathlib
namespace Brockian.KummerTheorem
/-- Kummer's theorem (digit-sum form): for a prime p, the p-adic valuation of C(m+n, m),
    times (p−1), equals S_p(m) + S_p(n) − S_p(m+n), where S_p is the base-p digit sum
    (equivalently, the number of carries when adding m and n in base p). -/
theorem kummer (p m n : ℕ) (hp : p.Prime) :
    (Nat.choose (m + n) m).factorization p * (p - 1) =
      (Nat.digits p m).sum + (Nat.digits p n).sum - (Nat.digits p (m + n)).sum := by
  have hchoose : Nat.choose (m + n) m * m.factorial * n.factorial = (m + n).factorial := by
    simpa using
      (Nat.choose_mul_factorial_mul_factorial (n := m + n) (k := m) (by omega))
  have hc : Nat.choose (m + n) m ≠ 0 := Nat.choose_ne_zero (by omega)
  have hfac := congrArg (fun x : ℕ => x.factorization p) hchoose
  dsimp only at hfac
  rw [Nat.factorization_mul (mul_ne_zero hc (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      Nat.factorization_mul hc (Nat.factorial_ne_zero _)] at hfac
  change (Nat.choose (m + n) m).factorization p + m.factorial.factorization p +
      n.factorial.factorization p = (m + n).factorial.factorization p at hfac
  have hm := Nat.sub_one_mul_factorization_factorial (n := m) hp
  have hn := Nat.sub_one_mul_factorization_factorial (n := n) hp
  have hmn := Nat.sub_one_mul_factorization_factorial (n := m + n) hp
  have hdm := Nat.digit_sum_le p m
  have hdn := Nat.digit_sum_le p n
  have hdmn := Nat.digit_sum_le p (m + n)
  have hm' : (p - 1) * m.factorial.factorization p + (p.digits m).sum = m := by
    omega
  have hn' : (p - 1) * n.factorial.factorization p + (p.digits n).sum = n := by
    omega
  have hmn' : (p - 1) * (m + n).factorial.factorization p +
      (p.digits (m + n)).sum = m + n := by
    omega
  have hmain : (Nat.choose (m + n) m).factorization p * (p - 1) +
      (p.digits (m + n)).sum = (p.digits m).sum + (p.digits n).sum := by
    nlinarith
  omega
end Brockian.KummerTheorem

