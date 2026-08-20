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

theorem moebius_sq_eq_sum_sq_divisors (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.moebius n) ^ 2
      = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), ArithmeticFunction.moebius d := by
  obtain ⟨s, r, rfl, hs⟩ := Nat.sq_mul_squarefree n
  have hr : r ≠ 0 := by rintro rfl; simp at hn
  have hs0 : s ≠ 0 := by rintro rfl; simp at hn
  rw [mul_comm] at hn ⊢
  rw [filter_sq_dvd hs hr hs0, sum_moebius_divisors r, moebius_sq_apply hs]

/-- **Liouville as Möbius over square-divisors.** For `n ≥ 1`,
`λ(n) = ∑_{d : d^2 ∣ n} μ(n / d^2)`.  (Dirichlet-series identity `L(λ,s) = ζ(2s)/ζ(s)`; equivalently
`λ = μ ⋆ 𝟙_squares`.  Multiplicative; check on prime powers.) -/
