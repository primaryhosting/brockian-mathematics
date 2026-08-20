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

open scoped BigOperators

/-- The Gibbs (Shannon) entropy of a probability vector `p`:
`S(p) = -∑ i, p i * log (p i)`. -/

lemma convex_nonneg_vectors (ι : Type*) : Convex ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} := by
  intro x hx y hy a b ha hb _ i
  have hxi : 0 ≤ x i := hx i
  have hyi : 0 ≤ y i := hy i
  have : 0 ≤ a * x i + b * y i := by positivity
  simpa using this

/-- The entropy is concave on the set of vectors with nonnegative entries. -/
