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

lemma nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rwa [hc] at h

