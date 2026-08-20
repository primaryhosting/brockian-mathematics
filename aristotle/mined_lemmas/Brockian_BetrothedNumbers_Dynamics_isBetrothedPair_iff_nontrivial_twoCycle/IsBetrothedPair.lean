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

def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1

/-- **Betrothed pairs are exactly the positive nontrivial 2-cycles of `partner`.**
A pair `(m, n)` is a betrothed pair iff both entries are positive, distinct, and
`partner` swaps them. -/
