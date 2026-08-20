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

theorem squarefree_divisor_count (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d) ^ 2 = 2 ^ n.primeFactors.card := by
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors Squarefree]
  have h2 : ∑ d ∈ n.divisors with ¬ Squarefree d, (ArithmeticFunction.moebius d) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    simp only [Finset.mem_filter] at hd
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd.2]
    ring
  rw [h2, add_zero, Finset.sum_congr rfl fun d hd =>
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree (Finset.mem_filter.mp hd).2]
  rw [Nat.sum_divisors_filter_squarefree hn]
  simp [Nat.factors_eq]

end BrockianParity

