/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter

namespace Frontier

/-- The `n`-th prime number (`primeSeq 0 = 2`). -/

noncomputable def primeSeq (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap `p_{n+1} - p_n`. -/
