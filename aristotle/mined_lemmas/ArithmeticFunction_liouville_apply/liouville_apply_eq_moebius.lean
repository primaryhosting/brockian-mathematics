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

lemma liouville_apply_eq_moebius {s r : ℕ} (hs : Squarefree s) (hr : r ≠ 0) (hs0 : s ≠ 0) :
    liouville (s * r ^ 2) = μ s := by
  rw [liouville_apply (by positivity), ArithmeticFunction.cardFactors_mul hs0 (by positivity),
    ArithmeticFunction.cardFactors_pow, moebius_apply_of_squarefree hs, pow_add, pow_mul]
  simp

/-- **Squarefree indicator via square-divisors.** For `n ≥ 1`,
`μ(n)^2 = ∑_{d : d^2 ∣ n} μ(d)`.  (`μ(n)^2` is 1 iff `n` is squarefree; the right side is the
classical convolution proof of that indicator.  Multiplicative on both sides; check on prime powers
`p^a`: RHS `= ∑_{2j ≤ a} μ(p^j) = 1 + (-1) = 0` for `a ≥ 2`, `= 1` for `a ∈ {0,1}`.) -/
