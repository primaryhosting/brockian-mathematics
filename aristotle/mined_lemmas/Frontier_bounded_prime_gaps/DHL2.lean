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

def DHL2 : Prop :=
  ∃ H : Finset ℕ, ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ 2 ≤ (H.filter (fun h => Nat.Prime (n + h))).card

