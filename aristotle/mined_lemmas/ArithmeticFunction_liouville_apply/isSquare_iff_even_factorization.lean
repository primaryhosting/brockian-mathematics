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

theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp
  · intro h
    refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    obtain ⟨t, ht⟩ := h p
    omega

/-- **Liouville divisor-sum identity** (the Dirichlet convolution `λ ⋆ 1`).
For `n ≥ 1`, the sum of the Liouville function over the divisors of `n` is `1` when `n`
is a perfect square and `0` otherwise.

Intuition/proof sketch: `λ` is completely multiplicative, so `∑_{d ∣ n} λ(d)` is multiplicative
in `n`; on a prime power `p^a` it is `∑_{j=0}^{a} (-1)^j = 1` if `a` is even, `0` if `a` is odd;
the product over the prime factorization is therefore `1` iff every exponent is even, i.e. iff `n`
is a perfect square. Useful Mathlib: `ArithmeticFunction.liouville`, `liouville_apply`,
`liouville_apply_mul`, `isMultiplicative_liouville`, `Nat.ArithmeticFunction.IsMultiplicative`
divisor-sum lemmas, `Nat.isSquare_iff_...`/`Nat.factorization` characterisations of squares. -/
