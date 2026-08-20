import Mathlib

/-!
# Two square-divisor identities (parity/sieve arithmetic)

Both use Mathlib's `ArithmeticFunction.moebius` (μ) and `ArithmeticFunction.liouville` (λ).
Neither identity is currently in Mathlib. Compile against a bare `import Mathlib`; do not cite
any non-core/Archive namespaces or invented lemmas.

The current Mathlib does not provide `ArithmeticFunction.liouville`, so it is defined here in the
`ArithmeticFunction` namespace in the standard way, `λ n = (-1) ^ Ω n`, where
`Ω = ArithmeticFunction.cardFactors` counts prime factors with multiplicity.

The proofs use the decomposition `n = s * r ^ 2` with `s` squarefree (`Nat.sq_mul_squarefree`).
Since `s` is squarefree, `d ^ 2 ∣ n ↔ d ∣ r`, so both sums are sums over the divisors of `r`.
-/

namespace ArithmeticFunction

open scoped ArithmeticFunction.Omega

/-- The **Liouville function** `λ n = (-1) ^ Ω n`, where `Ω n = ArithmeticFunction.cardFactors n`
counts the prime factors of `n` with multiplicity (and `λ 0 = 0`, as for every arithmetic
function). -/

lemma moebius_sq_apply {s r : ℕ} (hs : Squarefree s) :
    (μ (s * r ^ 2)) ^ 2 = if r = 1 then 1 else 0 := by
  by_cases h : r = 1
  · subst h
    simpa using moebius_sq_eq_one_of_squarefree (by simpa using hs)
  · rw [if_neg h, moebius_eq_zero_of_not_squarefree (not_squarefree_mul_sq h)]
    simp

/-- For a proper divisor `d` of `r`, the quotient `(s * r ^ 2) / d ^ 2` is not squarefree. -/
