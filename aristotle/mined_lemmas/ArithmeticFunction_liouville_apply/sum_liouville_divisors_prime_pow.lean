import Mathlib

/-!
# Parity/sieve arithmetic: two missing Liouville / Möbius divisor identities

Both statements are about the Liouville function `λ` (`ArithmeticFunction.liouville`) and the
Möbius function `μ` (`ArithmeticFunction.moebius`). The Möbius function is Mathlib's; the
Liouville function is *not* present in the Mathlib version pinned by this project, so it is
defined below in the `ArithmeticFunction` namespace, together with the facts that it is
completely multiplicative (`liouville_apply_mul`, `isMultiplicative_liouville`) and its value on
prime powers. Mathlib does not prove the classical square-indicator divisor identity below.
These are the arithmetic backbone of the parity phenomenon in sieve theory.
-/

namespace ArithmeticFunction

/-- The Liouville function `λ n = (-1) ^ Ω n` (with `λ 0 = 0`), where `Ω n` is the number of
prime factors of `n` counted with multiplicity.

Note: the current Mathlib version pinned by this project (`v4.28.0`) does not contain a
definition named `ArithmeticFunction.liouville`, so it is supplied here, in Mathlib's own
`ArithmeticFunction` namespace, exactly as the classical function. -/

theorem sum_liouville_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, liouville d = if Even k then 1 else 0 := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [liouville_prime_pow hp]
  rw [neg_one_geom_sum]
  rcases Nat.even_or_odd k with hk | hk
  · rw [if_pos hk, if_neg fun h => (Nat.even_add_one.mp h) hk]
  · have hk' : ¬ Even k := by simpa [Nat.not_even_iff_odd] using hk
    rw [if_neg hk', if_pos (Nat.even_add_one.mpr hk')]

end ArithmeticFunction

namespace BrockianParity

/-- A positive natural number is a square iff every exponent in its prime factorization
is even. -/
