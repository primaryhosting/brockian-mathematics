import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The sum of all (positive) divisors of `n`, i.e. `σ₁ n`. -/

lemma sigmaSum_5775 : sigmaSum 5775 = 11904 := by
  unfold sigmaSum
  decide

set_option maxRecDepth 100000 in
/-- `σ₁ 6128 = 11904`. -/
