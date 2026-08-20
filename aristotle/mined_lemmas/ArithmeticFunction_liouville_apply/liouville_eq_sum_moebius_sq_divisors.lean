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

theorem liouville_eq_sum_moebius_sq_divisors (n : ℕ) (hn : n ≠ 0) :
    ArithmeticFunction.liouville n
      = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), ArithmeticFunction.moebius (n / d ^ 2) := by
  obtain ⟨s, r, rfl, hs⟩ := Nat.sq_mul_squarefree n
  have hr : r ≠ 0 := by rintro rfl; simp at hn
  have hs0 : s ≠ 0 := by rintro rfl; simp at hn
  rw [mul_comm] at hn ⊢
  rw [filter_sq_dvd hs hr hs0, liouville_apply_eq_moebius hs hr hs0]
  rw [Finset.sum_eq_single r]
  · congr 1
    exact (Nat.mul_div_cancel s (by positivity : 0 < r ^ 2)).symm
  · intro d hd hdr
    exact moebius_div_sq_eq_zero hr (Nat.dvd_of_mem_divisors hd) hdr
  · intro h
    exact absurd (Nat.mem_divisors_self r hr) h

end BrockianSieve

