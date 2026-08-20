/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.BetrothedNumbers.Dynamics

/-- The *betrothed partner map*: `partner n = σ₁(n) - n - 1`, i.e. the sum of the
divisors of `n` other than `1` and `n` itself (natural subtraction). -/

def partner (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n - 1

/-- `m` and `n` form a *betrothed (quasi-amicable) pair*: they are distinct positive
integers with `σ₁(m) = σ₁(n) = m + n + 1`. -/
