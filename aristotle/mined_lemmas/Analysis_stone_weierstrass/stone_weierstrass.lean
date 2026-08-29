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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

/-- **Stone-Weierstrass theorem (polynomial form).**
On a compact interval `[a, b]`, the topological closure of the subalgebra of polynomial
functions inside the algebra `C([a,b], ℝ)` of continuous real-valued functions
(with the uniform topology) is the whole algebra. -/

theorem stone_weierstrass (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = (⊤ : Subalgebra ℝ C(Set.Icc a b, ℝ)) :=
  polynomialFunctions_closure_eq_top a b

/-- Uniform-approximation form of the Stone-Weierstrass theorem: every continuous function
on `[a, b]` is, for every `ε > 0`, uniformly approximated to within `ε` by a polynomial. -/
