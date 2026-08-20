import Mathlib
/-!
# Legendre sieve: main term with error bound.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve
/-- The count of integers in `[1, x]` coprime to `P` differs from the heuristic main term
`x · ∏_{p ∣ P} (1 − 1/p)` by at most `2^{ω(P)}` (the number of squarefree divisors of `P`).
(Sanity: `x=10, P=6`: count `=3`, main term `=10·(1/2)(2/3)=10/3`, `|3−10/3|=1/3 ≤ 4 = 2²`.)
Proof idea: count `= ∑_{d ∣ P} μ(d) ⌊x/d⌋` (Legendre); main term `= ∑_{d ∣ P} μ(d) · x/d`; the
difference is `∑_{d ∣ P} μ(d)(⌊x/d⌋ − x/d)` with each term of absolute value `< 1`, and there are
`2^{ω(P)}` nonzero (squarefree-`d`) terms. -/
theorem legendre_sieve_error (x P : ℕ) (hP : P ≠ 0) :
    |(((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℝ)
        - (x : ℝ) * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)|
      ≤ (2 : ℝ) ^ P.primeFactors.card := by
  sorry
end BrockianSieve
