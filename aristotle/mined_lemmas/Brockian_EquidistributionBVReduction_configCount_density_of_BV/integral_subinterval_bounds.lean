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

import Brockian.EquidistributionBVReduction

/-!
# An equidistributed sequence

This file exhibits a concrete sequence in `[0,1)` satisfying
`Brockian.EquidistributionBVReduction.Equidistributed`, showing that the equidistribution
hypothesis of `configCount_density_of_BV` is satisfiable (so the theorem is not vacuous).

The sequence is the "triangular block" sequence: the `k`-th block lists the `k+1` points
`0/(k+1), 1/(k+1), …, k/(k+1)`.
-/

open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- Start index of block `k`; block `k` consists of the `k+1` indices
`blockStart k, …, blockStart k + k`. -/

lemma integral_subinterval_bounds (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) {m i : ℕ}
    (hm : 0 < m) (hi : i < m) :
    f ((i:ℝ)/m)/m ≤ (∫ t in ((i:ℝ)/m)..(((i:ℝ)+1)/m), f t) ∧
    (∫ t in ((i:ℝ)/m)..(((i:ℝ)+1)/m), f t) ≤ f (((i:ℝ)+1)/m)/m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hi1 : (i:ℝ) + 1 ≤ m := by exact_mod_cast hi
  have hab : (i:ℝ)/m ≤ ((i:ℝ)+1)/m := by gcongr; linarith
  have hsub : Set.Icc ((i:ℝ)/m) (((i:ℝ)+1)/m) ⊆ Set.Icc (0:ℝ) 1 := by
    intro t ht
    refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
    rw [div_le_one hm']; exact hi1
  have hmono : MonotoneOn f (Set.uIcc ((i:ℝ)/m) (((i:ℝ)+1)/m)) := by
    rw [Set.uIcc_of_le hab]; exact hf.mono hsub
  have hint : IntervalIntegrable f MeasureTheory.volume ((i:ℝ)/m) (((i:ℝ)+1)/m) :=
    hmono.intervalIntegrable
  have hlen : ((i:ℝ)+1)/m - (i:ℝ)/m = 1/m := by field_simp; ring
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (f := fun _ => f ((i:ℝ)/m)) (g := f) hab intervalIntegrable_const hint
      (fun t ht => hf (hsub ⟨le_refl _, hab⟩) (hsub ht) ht.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h
    have heq : f ((i:ℝ)/m)/m = 1/(m:ℝ) * f ((i:ℝ)/m) := by ring
    rw [heq]; exact h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (f := f)
      (g := fun _ => f (((i:ℝ)+1)/m)) hab hint intervalIntegrable_const
      (fun t ht => hf (hsub ht) (hsub ⟨hab, le_refl _⟩) ht.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h
    have heq : f (((i:ℝ)+1)/m)/m = 1/(m:ℝ) * f (((i:ℝ)+1)/m) := by ring
    rw [heq]; exact h

/-- The integral over `[0,1]` splits along the uniform partition into `m` pieces. -/
