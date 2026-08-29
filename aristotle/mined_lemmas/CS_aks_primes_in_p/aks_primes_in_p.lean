import Mathlib

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace CS

/-- For `q` a prime factor of `n` with `q < n`, the product `∏_{i=1}^{q-1} (n - i)`
is not divisible by `q`. -/

theorem aks_primes_in_p (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a : ℕ, Nat.Coprime a n →
      (X + C (a : ZMod n)) ^ n = X ^ n + C ((a : ZMod n) ^ n) := by
  constructor
  · intro hp a _
    haveI : Fact n.Prime := ⟨hp⟩
    rw [add_pow_char, ← map_pow]
  · intro h
    by_contra hnp
    refine not_congr_of_not_prime hn hnp ?_
    have := h 1 (Nat.coprime_one_left n)
    simpa using this

/-- The classical special case of the AKS criterion: for `n ≥ 2`, `n` is prime if and only if
`(X + 1) ^ n = X ^ n + 1` in `(ZMod n)[X]`. -/
