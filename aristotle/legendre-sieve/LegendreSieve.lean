import Mathlib

/-!
# Legendre's sieve (inclusion–exclusion / sieve of Eratosthenes)

Uses Mathlib's `ArithmeticFunction.moebius` (μ). Compile against a bare `import Mathlib`; do not
cite any non-core/Archive namespaces or invented lemmas.
-/

namespace BrockianSieve

/-- **Legendre's sieve.** The number of integers in `[1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`.  Non-squarefree divisors contribute `0` (μ vanishes), so no squarefree
hypothesis on `P` is needed.  This is the foundational inclusion–exclusion identity of sieve theory.
(Sanity: `x = 10`, `P = 6`: LHS `= #{1,5,7} = 3`; RHS `= 10 − 5 − 3 + 1 = 3`.) -/
theorem legendre_sieve (x P : ℕ) (hP : P ≠ 0) :
    (((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℤ)
      = ∑ d ∈ P.divisors, ArithmeticFunction.moebius d * ((x / d : ℕ) : ℤ) := by
  sorry

end BrockianSieve
