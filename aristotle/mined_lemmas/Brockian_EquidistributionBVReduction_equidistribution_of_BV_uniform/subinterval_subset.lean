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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
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

namespace Brockian.EquidistributionBVReduction

open Filter Finset

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part is `< a`. -/

lemma subinterval_subset (k j : ℕ) (hk : 0 < k) (hj : j + 1 ≤ k) :
    Set.uIcc ((j:ℝ)/k) (((j:ℝ)+1)/k) ⊆ Set.Icc (0:ℝ) 1 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have h1 : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by
    rw [div_le_div_iff_of_pos_right hk0]; linarith
  rw [Set.uIcc_of_le h1]
  refine Set.Icc_subset_Icc (pt_mem k j hk (by omega)).1 ?_
  have hcast : ((j:ℝ)+1)/k = ((j+1 : ℕ):ℝ)/k := by push_cast; ring
  rw [hcast]
  exact (pt_mem k (j+1) hk hj).2

/-- A monotone function is interval integrable on each subinterval. -/
