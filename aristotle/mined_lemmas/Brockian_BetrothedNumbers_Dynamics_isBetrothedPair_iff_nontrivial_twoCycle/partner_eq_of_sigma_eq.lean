/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The *partner* (or quasi-aliquot) function: `partner n = σ₁(n) - n - 1`, the sum of the
proper divisors of `n` other than `1`.  Subtraction is truncated natural subtraction. -/

lemma partner_eq_of_sigma_eq {n k : ℕ} (h : (sigma 1) n = n + 1 + k) : partner n = k := by
  simp [partner_eq, h]

/-- Conversely, a *positive* value of `partner` determines `σ₁`. -/
