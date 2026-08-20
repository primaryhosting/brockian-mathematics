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

/-- `nthPrime n` is the `n`-th prime number, counting from `nthPrime 0 = 2`. -/

lemma nthPrime_succ_le_of_prime {k q : ℕ} (hq : q.Prime) (h : nthPrime k < q) :
    nthPrime (k + 1) ≤ q := by
  by_contra hcon
  push_neg at hcon
  exact absurd (Nat.le_nth_of_lt_nth_succ hcon hq) (not_le.2 h)

/-- **Reduction of bounded prime gaps to bounded prime pairs.**

If for some fixed `B` there are arbitrarily large primes `p` admitting a prime `q`
with `p < q ≤ p + B`, then the liminf of the prime gaps is finite. -/
