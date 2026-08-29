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

lemma nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  rwa [hc] at h

