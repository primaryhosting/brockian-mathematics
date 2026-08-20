import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.BetrothedNumbers

open Finset

set_option maxRecDepth 100000

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

def IsBetrothedPair (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a ≠ b ∧ sigma1 a = a + b + 1 ∧ sigma1 b = a + b + 1

instance (a b : ℕ) : Decidable (IsBetrothedPair a b) := by
  unfold IsBetrothedPair sigma1; infer_instance

/-- **The betrothed pair (5775, 6128)**, verified by kernel computation. -/
