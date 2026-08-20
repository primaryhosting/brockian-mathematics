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

lemma idx_eq_iff (x : ℕ → ℝ) (hk : 0 < k) (i n : ℕ) :
    idx x k n = i ↔ Int.fract (x n) ∈ Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ (k : ℝ) * Int.fract (x n) := by
    have := Int.fract_nonneg (x n); positivity
  rw [idx, Nat.floor_eq_iff h0]
  simp only [Set.mem_Ico, div_le_iff₀ hk', lt_div_iff₀ hk']
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

