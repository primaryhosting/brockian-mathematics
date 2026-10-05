/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean 4
does not allow a module docstring to precede the `import` commands.)
-/

open Filter

namespace Frontier

/-- The `n`-th prime number (`nthPrime 0 = 2`). -/

lemma nthPrime_succ_le_of_gap_le {n B : ℕ} (h : primeGap n ≤ B) :
    nthPrime (n + 1) ≤ nthPrime n + B := by
  have := nthPrime_lt_nthPrime_succ n
  unfold primeGap at h
  omega

/-- If `p` is prime and `q` is a larger prime, then the prime following `p` is at most `q`. -/
