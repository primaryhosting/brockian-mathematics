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

import Mathlib
/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The empirical frequency with which the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma riemann_sum_gap (f : ℝ → ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ i ∈ Finset.range k, f (((i : ℝ) + 1) / k) / k)
      - (∑ i ∈ Finset.range k, f ((i : ℝ) / k) / k) = (f 1 - f 0) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set g : ℕ → ℝ := fun j => f ((j : ℝ) / k) / k with hg
  have hcongr : ∀ i ∈ Finset.range k,
      f (((i : ℝ) + 1) / k) / k - f ((i : ℝ) / k) / k = g (i + 1) - g i := by
    intro i _
    simp only [hg]
    push_cast
    ring_nf
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hcongr, Finset.sum_range_sub g]
  simp only [hg]
  rw [div_self (ne_of_gt hk')]
  simp [sub_div]

/-- Equidistribution test for monotone functions. -/
