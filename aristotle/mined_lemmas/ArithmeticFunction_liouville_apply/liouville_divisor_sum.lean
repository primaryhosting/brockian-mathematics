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

theorem liouville_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ArithmeticFunction.liouville d = if IsSquare n then 1 else 0 := by
  have hmul : ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
      ArithmeticFunction.liouville).IsMultiplicative :=
    (ArithmeticFunction.IsMultiplicative.natCast ArithmeticFunction.isMultiplicative_zeta).mul
      ArithmeticFunction.isMultiplicative_liouville
  rw [← ArithmeticFunction.coe_zeta_mul_apply, hmul.multiplicative_factorization _ hn]
  have hfac : ∀ p ∈ n.factorization.support,
      ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * ArithmeticFunction.liouville)
          (p ^ n.factorization p)
        = if Even (n.factorization p) then 1 else 0 := by
    intro p hp
    rw [ArithmeticFunction.coe_zeta_mul_apply,
      ArithmeticFunction.sum_liouville_divisors_prime_pow
        (Nat.prime_of_mem_primeFactors (by simpa using hp))]
  rw [Finsupp.prod, Finset.prod_congr rfl hfac]
  by_cases hsq : IsSquare n
  · rw [if_pos hsq]
    exact Finset.prod_eq_one fun p _ => if_pos ((isSquare_iff_even_factorization hn).mp hsq p)
  · rw [if_neg hsq]
    obtain ⟨p, hp⟩ : ∃ p, ¬ Even (n.factorization p) := by
      by_contra h
      push_neg at h
      exact hsq ((isSquare_iff_even_factorization hn).mpr h)
    refine Finset.prod_eq_zero (i := p) ?_ (by rw [if_neg hp])
    simp only [Finsupp.mem_support_iff]
    intro h
    rw [h] at hp
    exact hp Even.zero

/-- **Squarefree-divisor count.** For `n ≥ 1`, `∑_{d ∣ n} μ(d)^2` counts the squarefree divisors
of `n`, which equals `2 ^ ω(n)` where `ω(n) = n.primeFactors.card` is the number of distinct
primes dividing `n`.

Intuition/proof sketch: `μ(d)^2 = 1` iff `d` is squarefree and `0` otherwise
(`moebius_sq_eq_one_of_squarefree`), so the sum counts squarefree divisors; a squarefree divisor is
exactly a product of a subset of the distinct prime factors, giving `2 ^ ω(n)`. -/
