import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate `m = (2^k - 1) * (p + 2)`. -/

theorem sigmaCriterion_iff (k p : ℕ) :
    SigmaCriterion k p ↔
      σ 1 (thabitCandidate k p) = thabitCandidate k p + thabitPartner k p + 1 := by
  rw [SigmaCriterion, sigmaCriterion_rhs_eq]

/-- **Thabit balance identity.** Under the delivered sigma criterion, the subtraction-free
balance `σ(m) + 2^(k+1) = 2m + (p + 3)` holds for `m = (2^k - 1)(p + 2)`. -/
