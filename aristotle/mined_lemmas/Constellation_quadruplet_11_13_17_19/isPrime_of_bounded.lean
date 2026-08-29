/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Constellation

/-- Primality of a natural number: `n` is at least `2` and its only divisors are `1` and `n`.

This file is required to begin with the header comment above, which Lean parses as a module
documentation command; consequently no `import` line may follow it, so the development below is
carried out with the Lean core library only, and primality is spelled out explicitly here
(this predicate is equivalent to Mathlib's `Nat.Prime`). -/

theorem isPrime_of_bounded (n : Nat) (h2 : 2 ≤ n)
    (h : ∀ m, m < n + 1 → m ∣ n → m = 1 ∨ m = n) : IsPrime n := by
  refine ⟨h2, fun m hm => h m ?_ hm⟩
  have := Nat.le_of_dvd (by omega) hm
  omega

