import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

theorem density_zero_reduction
    (hcore : ∀ K : ℕ, HasDensityZero {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}) :
    HasDensityZero Betrothed :=
  hasDensityZero_of_countUpTo_le 2 (hasDensityZero_betrothedSmall hcore) countUpTo_betrothed_le

end BetrothedNumbers
end Brockian

