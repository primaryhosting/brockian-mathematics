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

lemma riemann_gap (g : ℝ → ℝ) (hm : 0 < m) :
    ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * (1 / m)
      - ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * (1 / m) = (g 1 - g 0) / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [← Finset.sum_sub_distrib]
  have key := Finset.sum_range_sub (fun i : ℕ => g ((i:ℝ)/m) * (1/m)) m
  have hcongr : ∀ i ∈ Finset.range m,
      g (((i : ℝ) + 1) / m) * (1 / m) - g ((i : ℝ) / m) * (1 / m)
        = (fun i : ℕ => g ((i:ℝ)/m) * (1/m)) (i+1) - (fun i : ℕ => g ((i:ℝ)/m) * (1/m)) i := by
    intro i _
    simp only
    push_cast
    ring
  rw [Finset.sum_congr rfl hcongr, key]
  simp only [Nat.cast_zero, zero_div, div_self (ne_of_gt hm')]
  ring

end Riemann

section Limits

variable {g : ℝ → ℝ} {x : ℕ → ℝ} {m : ℕ}

