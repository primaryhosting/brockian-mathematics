import Mathlib

/-!
# Two square-divisor identities (parity/sieve arithmetic)

Both use Mathlib's `ArithmeticFunction.moebius` (μ) and `ArithmeticFunction.liouville` (λ).
Neither identity is currently in Mathlib. Compile against a bare `import Mathlib`; do not cite
any non-core/Archive namespaces or invented lemmas.
-/

namespace BrockianSieve

/-- **Squarefree indicator via square-divisors.** For `n ≥ 1`,
`μ(n)^2 = ∑_{d : d^2 ∣ n} μ(d)`.  (`μ(n)^2` is 1 iff `n` is squarefree; the right side is the
classical convolution proof of that indicator.  Multiplicative on both sides; check on prime powers
`p^a`: RHS `= ∑_{2j ≤ a} μ(p^j) = 1 + (-1) = 0` for `a ≥ 2`, `= 1` for `a ∈ {0,1}`.) -/
theorem moebius_sq_eq_sum_sq_divisors (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.moebius n) ^ 2
      = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), ArithmeticFunction.moebius d := by
  sorry

/-- **Liouville as Möbius over square-divisors.** For `n ≥ 1`,
`λ(n) = ∑_{d : d^2 ∣ n} μ(n / d^2)`.  (Dirichlet-series identity `L(λ,s) = ζ(2s)/ζ(s)`; equivalently
`λ = μ ⋆ 𝟙_squares`.  Multiplicative; check on prime powers.) -/
theorem liouville_eq_sum_moebius_sq_divisors (n : ℕ) (hn : n ≠ 0) :
    ArithmeticFunction.liouville n
      = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), ArithmeticFunction.moebius (n / d ^ 2) := by
  sorry

end BrockianSieve
