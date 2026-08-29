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

open scoped Polynomial

/-- **Stone–Weierstrass theorem (polynomial form).**

On a compact interval `[a, b] ⊆ ℝ`, the subalgebra of polynomial functions is dense in the
algebra `C([a,b], ℝ)` of continuous real-valued functions with the uniform norm: its
topological closure is the whole space. -/

theorem stone_weierstrass_dense (a b : ℝ) :
    Dense (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) := by
  rw [dense_iff_closure_eq]
  have h : (((polynomialFunctions (Set.Icc a b)).topologicalClosure : Subalgebra ℝ _) :
      Set C(Set.Icc a b, ℝ)) = ((⊤ : Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set _) := by
    rw [stone_weierstrass a b]
  simpa [Subalgebra.topologicalClosure_coe] using h

/-- Epsilon form of `Analysis.stone_weierstrass`: every function `f : ℝ → ℝ` that is continuous
on `[a, b]` can be uniformly approximated on `[a, b]`, to within any `ε > 0`, by a polynomial. -/
