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

lemma sq_dvd_iff_dvd {s r : ℕ} (hs : Squarefree s) (hr : r ≠ 0) (d : ℕ) :
    d ^ 2 ∣ s * r ^ 2 ↔ d ∣ r := by
  have hs0 : s ≠ 0 := hs.ne_zero
  have hn0 : s * r ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at h
      omega
    rw [← Nat.factorization_le_iff_dvd hd0 hr]
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hn0] at h
    intro p
    have h1 := h p
    simp [Nat.factorization_mul hs0 (pow_ne_zero 2 hr), Nat.factorization_pow] at h1 ⊢
    have h2 : s.factorization p ≤ 1 := hs.natFactorization_le_one p
    omega
  · intro h
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd h 2) s

/-- The square-divisor filter of `s * r ^ 2` (with `s` squarefree) is `r.divisors`. -/
