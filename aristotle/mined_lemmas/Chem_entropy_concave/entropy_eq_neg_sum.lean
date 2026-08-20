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

namespace Chem

/-- The Gibbs entropy of a probability vector `p`, `-∑ i, p i * log (p i)`. -/

lemma entropy_eq_neg_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = -∑ i, p i * Real.log (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- The Gibbs entropy `-∑ pᵢ log pᵢ` is concave on the probability simplex. -/
