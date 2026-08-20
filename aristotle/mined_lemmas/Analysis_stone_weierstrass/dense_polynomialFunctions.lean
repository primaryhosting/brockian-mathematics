/-
# Stone Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.stone_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stone Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.stone_weierstrass
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

/-- Key intermediate lemma: the set of polynomial functions on a compact interval `[a,b]`
is dense in the space `C([a,b], ℝ)` of continuous functions with the uniform (sup) norm. -/

theorem dense_polynomialFunctions (a b : ℝ) :
    Dense ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := by
  rw [dense_iff_closure_eq]
  have h := polynomialFunctions_closure_eq_top a b
  have h' : ((polynomialFunctions (Set.Icc a b)).topologicalClosure :
      Set C(Set.Icc a b, ℝ)) = ((⊤ : Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set _) := by
    rw [h]
  simpa using h'

/-- Second intermediate step: every continuous function on `[a,b]` can be uniformly
approximated to arbitrary precision by a polynomial function. -/
