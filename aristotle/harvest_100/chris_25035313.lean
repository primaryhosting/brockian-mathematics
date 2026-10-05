import Mathlib
/-!
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Polynomial

/-- **Fundamental theorem of algebra.**
Every nonconstant complex polynomial has a complex root.
Here "nonconstant" is expressed as `p.natDegree ≠ 0`. -/
theorem fta_algebra (p : Polynomial ℂ) (hp : p.natDegree ≠ 0) :
    ∃ z : ℂ, p.eval z = 0 := by
  refine Complex.exists_root ?_
  rcases eq_or_ne p 0 with rfl | hp0
  · simp at hp
  · exact natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hp)

/-- Variant of the fundamental theorem of algebra where "nonconstant" is expressed as
"`p` is not of the form `C c`". -/
theorem fta_algebra' (p : Polynomial ℂ) (hp : ∀ c : ℂ, p ≠ C c) :
    ∃ z : ℂ, p.eval z = 0 := by
  refine fta_algebra p fun h => ?_
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp h
  exact hp c hc.symm

end Math

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

