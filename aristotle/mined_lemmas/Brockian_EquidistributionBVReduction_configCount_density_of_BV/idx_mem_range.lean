import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `S`:
the count of "configurations" of the first `N` terms of the sequence inside the window `S`. -/

lemma idx_mem_range (x : ℕ → ℝ) (hk : 0 < k) (n : ℕ) : idx x k n ∈ Finset.range k := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) * Int.fract (x n) := by
    have := Int.fract_nonneg (x n); positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (k : ℝ) * Int.fract (x n) < (k : ℕ) := by
    have := Int.fract_lt_one (x n); nlinarith
  simpa [idx, Finset.mem_range] using (Nat.floor_lt h0).2 h1

/-- The configuration count of the `i`-th window is the cardinality of the `i`-th fiber
of the index map. -/
