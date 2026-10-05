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

def TwoPrimesInBoundedWindow : Prop :=
  ∃ B : ℕ, ∀ N : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N ≤ p ∧ p < q ∧ q ≤ p + B

/-- The Goldston–Pintz–Yıldırım / Zhang / Maynard statement `DHL[k, 2]`: there is a finite
set of shifts `H` (in the applications, an admissible `k`-tuple) such that for arbitrarily
large `n` at least two of the numbers `n + h`, `h ∈ H`, are prime. -/
