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

lemma not_squarefree_mul_sq {s m : ℕ} (hm : m ≠ 1) : ¬ Squarefree (s * m ^ 2) := by
  intro hsq
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm
  have hdvd : p * p ∣ s * m ^ 2 :=
    Dvd.dvd.mul_left (by rw [sq]; exact mul_dvd_mul hpm hpm) s
  exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hdvd))

/-- If `s` is squarefree then the `d` with `d ^ 2 ∣ s * r ^ 2` are exactly the divisors of `r`. -/
