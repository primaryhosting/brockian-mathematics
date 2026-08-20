import Mathlib
/-!
# Euler totient as a Möbius convolution.
Uses Mathlib's `Nat.totient` and `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve
/-- Euler's totient as the Dirichlet convolution `φ = μ ⋆ id`:
`φ(n) = ∑_{d ∣ n} μ(d) · (n / d)`.  (Sanity: `n=6`: `φ(6)=2`; RHS `= 6 − 3 − 2 + 1 = 2`.) -/
theorem totient_eq_sum_moebius (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℤ)
      = ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d : ℕ) : ℤ) := by
  sorry
end BrockianSieve
