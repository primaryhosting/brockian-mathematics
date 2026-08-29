import Mathlib
import RequestProject.Brockian.EquidistributionBVReduction

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

open Filter Finset Set
open scoped Topology BigOperators Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace EquidistributionBVReduction

/-- `countIn x a b N` is the number of indices `n < N` with `x n ∈ [a, b)`. -/

lemma upper_sub_lower (hk : 0 < k) :
    (∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) * (1 / (k : ℝ))) -
        (∑ j ∈ Finset.range k, g ((j : ℝ) / k) * (1 / (k : ℝ))) = (g 1 - g 0) / k := by
  have h := Finset.sum_range_sub (f := fun j : ℕ => g ((j : ℝ) / k) * (1 / (k : ℝ))) (n := k)
  rw [← Finset.sum_sub_distrib]
  have hcongr : ∀ j ∈ Finset.range k,
      g (((j : ℝ) + 1) / k) * (1 / (k : ℝ)) - g ((j : ℝ) / k) * (1 / (k : ℝ))
        = (fun j : ℕ => g ((j : ℝ) / k) * (1 / (k : ℝ))) (j + 1)
          - (fun j : ℕ => g ((j : ℝ) / k) * (1 / (k : ℝ))) j := by
    intro j _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcongr, h]
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [Nat.cast_zero, zero_div, div_self hk']
  ring

/-- Koksma's theorem for monotone functions: along a uniformly distributed sequence the
Cesàro averages of a monotone function converge to its integral. -/
