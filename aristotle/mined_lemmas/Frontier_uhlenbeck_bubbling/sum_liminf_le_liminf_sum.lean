import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Filter MeasureTheory Metric

/-! ## Auxiliary lemmas -/

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/

theorem sum_liminf_le_liminf_sum {ι : Type*} (t : Finset ι) (f : ι → ℕ → ENNReal) :
    ∑ i ∈ t, liminf (fun n => f i n) atTop ≤ liminf (fun n => ∑ i ∈ t, f i n) atTop := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (add_le_add_left ih _) ?_
      refine le_trans (liminf_add_le_liminf_add_nat _ _) ?_
      refine liminf_le_liminf ?_
      filter_upwards with n
      rw [Finset.sum_insert ha]

/-- A finite set in a metric space can be surrounded by pairwise disjoint balls of a common
positive radius. -/
