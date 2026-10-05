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

lemma nth_prime_two : Nat.nth Nat.Prime 2 = 5 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 5) (by norm_num)
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  rwa [hc] at h

/-- Base case: the first prime gap is `3 - 2 = 1`. -/
