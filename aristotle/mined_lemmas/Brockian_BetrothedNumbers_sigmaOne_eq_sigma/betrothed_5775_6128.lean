import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/

theorem betrothed_5775_6128 : IsBetrothedPair 5775 6128 :=
  ⟨by norm_num, by norm_num, by norm_num, by rw [sigmaOne_5775], by rw [sigmaOne_6128]⟩

section Criterion

