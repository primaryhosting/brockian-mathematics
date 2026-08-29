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

lemma nth_succ_count_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) ≤ q := by
  have h1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    rw [Nat.count_succ, if_pos hp]
  have h2 : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q := by
    rw [← h1]; exact Nat.count_monotone _ hpq
  calc Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1)
      ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) := (Nat.nth_le_nth primes_infinite).2 h2
    _ = q := Nat.nth_count hq

/-- `DHL[k,2]` implies that two primes occur in a window of bounded length, arbitrarily
far out. -/
