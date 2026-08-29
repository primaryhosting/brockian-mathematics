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

lemma sum_indicator_eq_one (hm : 0 < m) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∑ i ∈ Finset.range m,
        (if y ∈ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) then (1 : ℝ) else 0) = 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hlt : ⌊y * m⌋₊ < m := by
    apply Nat.floor_lt' (by omega) |>.mpr
    calc y * m < 1 * m := by nlinarith
      _ = m := by ring
  have hcongr : ∀ i ∈ Finset.range m,
      (if y ∈ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) then (1 : ℝ) else 0)
        = (if ⌊y * m⌋₊ = i then (1:ℝ) else 0) := by
    intro i _
    simp only [mem_Ico_iff_floor hm hy0 i]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
  simp [Finset.mem_range, hlt]

end Partition

section Sandwich

variable {g : ℝ → ℝ} {x : ℕ → ℝ} {m N : ℕ}

/-- Lower step-function bound for the total sum. -/
