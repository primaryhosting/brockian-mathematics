import Mathlib
/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, the gap between the `n`-th and `(n+1)`-st prime
(with `p_0 = 2`, i.e. `p_n = Nat.nth Nat.Prime n`). -/

def TwinPrimeConjecture : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ (p + 2).Prime

/-- The twin prime conjecture implies `DHL[k,2]` (with the admissible pair `{0, 2}`), and
hence bounded prime gaps. -/
