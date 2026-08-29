import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
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

/-- A two-valued splitting lemma: if a set is infinite, one of the two colour classes
determined by a `Bool`-valued function is infinite. -/

lemma elt_color {k l : ℕ} (h : k < l) : c (elt c k) (elt c l) = col c (seqSet c k) := by
  have hmem : elt c l ∈ seqSet c (k + 1) := seqSet_antitone c h (elt_mem c l)
  exact col_of_mem_nextSet c hmem

