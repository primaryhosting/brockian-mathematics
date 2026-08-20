import Mathlib
namespace C5.NT7

open ArithmeticFunction Finset

open scoped sigma

/-- `σ 1 (2 ^ k) = 2 ^ (k + 1) - 1`, i.e. the sum of divisors of a power of two is the
corresponding Mersenne number. -/

theorem totient_prime (p : ℕ) (hp : p.Prime) : Nat.totient p = p - 1 :=
  Nat.totient_prime hp

end C5.NT7

