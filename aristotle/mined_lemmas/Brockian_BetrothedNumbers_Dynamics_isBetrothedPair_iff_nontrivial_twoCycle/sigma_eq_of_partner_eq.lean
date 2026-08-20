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

lemma sigma_eq_of_partner_eq {n k : ℕ} (hk : 0 < k) (h : partner n = k) :
    (sigma 1) n = n + 1 + k := by
  rw [partner_eq] at h
  omega

/-- **Characterization of betrothed pairs as nontrivial positive `2`-cycles of `partner`.**

A pair `(m, n)` is a betrothed pair exactly when `m` and `n` are distinct positive naturals
with `partner m = n` and `partner n = m`. -/
