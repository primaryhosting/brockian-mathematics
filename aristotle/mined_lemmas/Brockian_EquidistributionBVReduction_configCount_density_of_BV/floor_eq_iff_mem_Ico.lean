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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.EquidistributionBVReduction

open Filter Set MeasureTheory

/-- `configCount x S N` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` lands in the "configuration window" `S`. -/

lemma floor_eq_iff_mem_Ico {t : ℝ} (ht : 0 ≤ t) {i k : ℕ} (hk : 0 < k) :
    ⌊t * k⌋₊ = i ↔ t ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Nat.floor_eq_iff (by positivity)]
  rw [Set.mem_Ico, div_le_iff₀ hkpos, lt_div_iff₀ hkpos]

