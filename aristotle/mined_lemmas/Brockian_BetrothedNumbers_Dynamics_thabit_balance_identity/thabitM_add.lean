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

lemma thabitM_add (k p : ℕ) : thabitM k p + (p + 2) = 2 ^ k * (p + 2) := by
  unfold thabitM
  rw [Nat.sub_mul, one_mul]
  exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k))

/-- Subtraction-free description of `thabitPartner`. -/
