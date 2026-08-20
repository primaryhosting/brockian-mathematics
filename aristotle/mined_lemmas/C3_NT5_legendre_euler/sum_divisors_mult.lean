import Mathlib
namespace C3.NT5

/-- Euler's criterion: the Legendre symbol `(a/p)`, viewed in `ZMod p`, equals
`a ^ ((p-1)/2)` for an odd prime `p`. -/

theorem sum_divisors_mult (m n : ℕ) (h : Nat.Coprime m n) :
    ArithmeticFunction.sigma 1 (m * n)
      = ArithmeticFunction.sigma 1 m * ArithmeticFunction.sigma 1 n :=
  (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

/-- Wilson's theorem: `(p-1)! ≡ -1 [MOD p]` for a prime `p`. -/
