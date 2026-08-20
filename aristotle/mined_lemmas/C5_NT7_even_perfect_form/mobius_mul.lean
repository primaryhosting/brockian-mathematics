import Mathlib
namespace C5.NT7

open ArithmeticFunction Finset

open scoped sigma

/-- `σ 1 (2 ^ k) = 2 ^ (k + 1) - 1`, i.e. the sum of divisors of a power of two is the
corresponding Mersenne number. -/

theorem mobius_mul (m n : ℕ) (h : Nat.Coprime m n) :
    ArithmeticFunction.moebius (m*n) = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
  ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h

