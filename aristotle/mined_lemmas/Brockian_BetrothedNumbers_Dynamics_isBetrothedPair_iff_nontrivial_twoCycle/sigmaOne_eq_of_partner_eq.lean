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

set_option autoImplicit false

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`, i.e. `ArithmeticFunction.sigma 1`. -/

lemma sigmaOne_eq_of_partner_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : partner m = n) : sigmaOne m = m + n + 1 := by
  have hle : m ≤ sigmaOne m := le_sigmaOne hm
  rw [partner] at h
  omega

/--
**Characterization of betrothed pairs as nontrivial positive 2-cycles.**

`(m, n)` is a betrothed pair exactly when `m` and `n` are positive, distinct, and form a
2-cycle of the partner map `partner n = σ₁(n) - n - 1`.
-/
