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

lemma tendsto_count_div (hx : EquidistributedMod1 x) (hm : 0 < m) {i : ℕ}
    (hi : i ∈ Finset.range m) :
    Tendsto (fun N : ℕ => (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N)
      atTop (𝓝 (1 / m)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have him : (i : ℝ) + 1 ≤ m := by
    have : i + 1 ≤ m := Finset.mem_range.mp hi
    exact_mod_cast this
  have h := hx ((i : ℝ) / m) (((i : ℝ) + 1) / m) (by positivity)
    (by gcongr; linarith) (by rw [div_le_one hm']; exact him)
  have hdiff : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by
    field_simp
    ring
  rwa [hdiff] at h

/-- The lower step-function averages converge to the lower Riemann sum. -/
