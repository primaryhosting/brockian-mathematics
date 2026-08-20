import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate `m = (2^k - 1)(p + 2)`. -/

theorem thabit_balance_identity_iff (k p : ℕ) :
    sigma 1 (thabitM k p) + 2 ^ (k + 1) = 2 * thabitM k p + (p + 3) ↔ SigmaCriterion k p := by
  refine ⟨fun h => ?_, thabit_balance_identity k p⟩
  have hm := thabitM_add k p
  have hpart := thabitPartner_add k p
  have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
  rw [hpow] at h
  rw [SigmaCriterion]
  omega

/-- Deficiency comparison: `m` is deficient iff `p + 3 < 2^(k+1)`. -/
