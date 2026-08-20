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

lemma moebius_div_sq_eq_zero {s r d : ℕ} (hr : r ≠ 0) (hd : d ∣ r) (hdr : d ≠ r) :
    μ ((s * r ^ 2) / d ^ 2) = 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 1 := by rintro rfl; simp at hdr
  have hd0 : d ≠ 0 := by rintro rfl; simp at hr
  have heq : (s * (d * k) ^ 2) / d ^ 2 = s * k ^ 2 := by
    rw [mul_pow, ← mul_assoc, mul_comm s (d ^ 2), mul_assoc,
      Nat.mul_div_cancel_left _ (by positivity)]
  rw [heq, moebius_eq_zero_of_not_squarefree (not_squarefree_mul_sq hk)]

/-- `λ (s * r ^ 2) = μ s` for `s` squarefree: the square factor does not change the parity of the
number of prime factors. -/
