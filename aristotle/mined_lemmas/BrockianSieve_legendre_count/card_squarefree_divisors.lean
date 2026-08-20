import Mathlib
/-!
# Legendre sieve: main term with error bound.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve

open ArithmeticFunction Finset

/-- Legendre's identity: the number of `n ∈ [1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`. -/

lemma card_squarefree_divisors (P : ℕ) (hP : P ≠ 0) :
    (P.divisors.filter Squarefree).card = 2 ^ P.primeFactors.card := by
  have h := Nat.sum_divisors_filter_squarefree (n := P) hP (f := fun _ => (1 : ℕ))
  have h2 : (UniqueFactorizationMonoid.normalizedFactors P).toFinset = P.primeFactors := by
    rw [Nat.factors_eq]; rfl
  simpa [h2, Finset.card_powerset] using h

/-- Each term `μ(d)(⌊x/d⌋ - x/d)` has absolute value at most `1`, and vanishes unless `d`
is squarefree. -/
