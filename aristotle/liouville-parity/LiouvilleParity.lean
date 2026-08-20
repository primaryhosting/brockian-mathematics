import Mathlib

/-!
# Parity/sieve arithmetic: two missing Liouville / Möbius divisor identities

Both statements use Mathlib's existing `ArithmeticFunction.liouville` (λ) and
`ArithmeticFunction.moebius` (μ). Mathlib already proves λ is completely multiplicative
(`liouville_apply_mul`, `isMultiplicative_liouville`) but does NOT prove the classical
square-indicator divisor identity below. These are the arithmetic backbone of the parity
phenomenon in sieve theory.
-/

namespace BrockianParity

/-- **Liouville divisor-sum identity** (the Dirichlet convolution `λ ⋆ 1`).
For `n ≥ 1`, the sum of the Liouville function over the divisors of `n` is `1` when `n`
is a perfect square and `0` otherwise.

Intuition/proof sketch: `λ` is completely multiplicative, so `∑_{d ∣ n} λ(d)` is multiplicative
in `n`; on a prime power `p^a` it is `∑_{j=0}^{a} (-1)^j = 1` if `a` is even, `0` if `a` is odd;
the product over the prime factorization is therefore `1` iff every exponent is even, i.e. iff `n`
is a perfect square. Useful Mathlib: `ArithmeticFunction.liouville`, `liouville_apply`,
`liouville_apply_mul`, `isMultiplicative_liouville`, `Nat.ArithmeticFunction.IsMultiplicative`
divisor-sum lemmas, `Nat.isSquare_iff_...`/`Nat.factorization` characterisations of squares. -/
theorem liouville_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ArithmeticFunction.liouville d = if IsSquare n then 1 else 0 := by
  sorry

/-- **Squarefree-divisor count.** For `n ≥ 1`, `∑_{d ∣ n} μ(d)^2` counts the squarefree divisors
of `n`, which equals `2 ^ ω(n)` where `ω(n) = n.primeFactors.card` is the number of distinct
primes dividing `n`.

Intuition/proof sketch: `μ(d)^2 = 1` iff `d` is squarefree and `0` otherwise
(`moebius_sq_eq_one_of_squarefree`), so the sum counts squarefree divisors; a squarefree divisor is
exactly a product of a subset of the distinct prime factors, giving `2 ^ ω(n)`. -/
theorem squarefree_divisor_count (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d) ^ 2 = 2 ^ n.primeFactors.card := by
  sorry

end BrockianParity
