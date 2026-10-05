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

def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- A finite criterion for primality: it suffices to check the divisors below `n + 1`. -/
