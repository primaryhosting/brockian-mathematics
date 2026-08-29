import Brockian.EquidistributionBVReduction

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

/-
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Filter Topology
open scoped BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma mem_Ico_iff_floor (hm : 0 < m) (hy : 0 ≤ y) (i : ℕ) :
    y ∈ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) ↔ ⌊y * m⌋₊ = i := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [Nat.floor_eq_iff (by positivity)]
  rw [Set.mem_Ico, div_le_iff₀ hm', lt_div_iff₀ hm']

