import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers.Dynamics

/-- The divisor-sum function `σ = σ₁`, `σ m = ∑ d ∣ m, d`. -/

lemma thabit_balance_witness :
    (75 : ℕ) + (3 + 2) = 2 ^ 4 * (3 + 2) ∧
      sigmaOne 75 + (3 + 1) = 2 ^ (4 + 1) * (3 + 1) := by
  refine ⟨by norm_num, ?_⟩
  rw [sigmaOne_eq_sum]
  decide

/-- At the witness above, `p + 3 = 6 < 32 = 2 ^ 5`, so the comparison theorem
yields that `75` is deficient. -/
