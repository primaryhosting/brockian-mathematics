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

theorem liouville_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    liouville (p ^ k) = (-1) ^ k := by
  rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]

/-- Local factor: the sum of `λ` over the divisors of a prime power. -/
