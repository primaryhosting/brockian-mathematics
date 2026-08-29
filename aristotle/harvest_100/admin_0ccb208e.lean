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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionBVReduction

open Filter Finset

/-- The set of *configurations* of size `N`: pairs `(a, b)` of indices below `N`
whose total weight `a + b` still fits below the cut-off `N`.  This is the lattice
simplex that arises as the admissible index set in the bounded-variation reduction
step of an equidistribution argument. -/
def configSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)

/-- The number of configurations of size `N`. -/
def configCount (N : ℕ) : ℕ := (configSet N).card

/-- The predicted main term for `configCount N`, namely the volume `N ^ 2 / 2`
of the continuous simplex `{(x, y) : x, y ≥ 0, x + y ≤ N}`. -/
noncomputable def mainTerm (N : ℕ) : ℝ := (N : ℝ) ^ 2 / 2

/-- Fibering the configuration set over its first coordinate. -/
lemma configCount_eq_sum (N : ℕ) :
    configCount N = ∑ a ∈ Finset.range N, (N - a) := by
  rw [configCount, configSet, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_filter]
  have h : {i ∈ Finset.range N | (a, i).1 + (a, i).2 < N} = Finset.range (N - a) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h, Finset.card_range]

/-- The Gauss summation for the fibre sizes, proved by induction on `N`. -/
lemma two_mul_sum_sub (N : ℕ) : 2 * (∑ a ∈ Finset.range N, (N - a)) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ, Nat.sub_zero]
    rw [Nat.mul_add, ih]
    ring

/-- Exact evaluation of the configuration count: `2 * configCount N = N * (N + 1)`. -/
lemma two_mul_configCount (N : ℕ) : 2 * configCount N = N * (N + 1) := by
  rw [configCount_eq_sum, two_mul_sum_sub]

/-- Real-valued form of the exact count. -/
lemma configCount_cast (N : ℕ) : (configCount N : ℝ) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  have h : ((2 * configCount N : ℕ) : ℝ) = ((N * (N + 1) : ℕ) : ℝ) := by
    rw [two_mul_configCount]
  push_cast at h
  linarith

/-- **Main result.** The configuration count is asymptotic to its main term:
`configCount N / mainTerm N → 1` as `N → ∞`. -/
theorem configCount_over_main_tendsto :
    Tendsto (fun N : ℕ => (configCount N : ℝ) / mainTerm N) atTop (nhds 1) := by
  have h0 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Tendsto (fun N : ℕ => (1 : ℝ) + 1 / (N : ℝ)) atTop (nhds 1) := by
    simpa using h0.const_add (1 : ℝ)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  rw [configCount_cast, mainTerm]
  field_simp

end Brockian.EquidistributionBVReduction

