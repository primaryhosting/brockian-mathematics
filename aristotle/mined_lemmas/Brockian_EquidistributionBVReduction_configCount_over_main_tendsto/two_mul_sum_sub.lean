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

lemma two_mul_sum_sub (N : ℕ) : 2 * (∑ a ∈ Finset.range N, (N - a)) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ, Nat.sub_zero]
    rw [Nat.mul_add, ih]
    ring

/-- Exact evaluation of the configuration count: `2 * configCount N = N * (N + 1)`. -/
