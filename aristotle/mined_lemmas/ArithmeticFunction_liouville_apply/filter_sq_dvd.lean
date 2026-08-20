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

lemma filter_sq_dvd {s r : ℕ} (hs : Squarefree s) (hr : r ≠ 0) (hs0 : s ≠ 0) :
    (s * r ^ 2).divisors.filter (fun d => d ^ 2 ∣ s * r ^ 2) = r.divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, sq_dvd_iff_dvd hs hr]
  constructor
  · rintro ⟨-, hd⟩
    exact ⟨hd, hr⟩
  · rintro ⟨hd, -⟩
    exact ⟨⟨Dvd.dvd.mul_left (hd.trans (dvd_pow_self r two_ne_zero)) s, by positivity⟩, hd⟩

/-- `∑_{d ∣ r} μ d = [r = 1]`. -/
