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

theorem isPrime_iff_nat_prime (n : ℕ) : IsPrime n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, h⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    rcases h m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- `(11, 13, 17, 19)` is a prime quadruplet of pattern `(0, 2, 6, 8)`, stated with Mathlib's
`Nat.Prime`. -/
