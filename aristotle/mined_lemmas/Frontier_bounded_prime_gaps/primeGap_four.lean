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

theorem primeGap_four : primeGap 4 = 2 := by
  simp [primeGap, primeSeq_four, primeSeq_five]

end BaseCases

/-- **Bounded prime gaps** (Zhang, Maynard–Tao), as a Lean-checked reduction.

Granted the arithmetic input `H` — that for some positive shift `d` there are infinitely many
primes `p` with `p + d` also prime (this is exactly what the Zhang / Maynard–Tao theorem
provides) — the sequence of prime gaps `p_{n+1} - p_n` has finite `liminf`, and indeed some
bound is attained by infinitely many gaps. -/
