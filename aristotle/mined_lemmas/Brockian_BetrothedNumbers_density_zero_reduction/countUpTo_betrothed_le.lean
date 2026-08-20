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

lemma countUpTo_betrothed_le (N : ℕ) :
    (countUpTo Betrothed N : ℝ) ≤ 2 * countUpTo BetrothedSmall N := by
  have h1 : countUpTo Betrothed N ≤ countUpTo (BetrothedSmall ∪ BetrothedLarge) N :=
    countUpTo_mono betrothed_subset_union N
  have h2 := countUpTo_union_le BetrothedSmall BetrothedLarge N
  have h3 := countUpTo_large_le_small N
  have : countUpTo Betrothed N ≤ 2 * countUpTo BetrothedSmall N := by omega
  exact_mod_cast this

/-- Splitting the smaller members by abundancy. -/
