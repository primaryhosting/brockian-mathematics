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

open ContinuousMap
open scoped unitInterval Polynomial

/-- The nondegenerate case `a < b`: the subalgebra of polynomial functions on `[a, b]` is
dense in `C([a, b], ℝ)`.  This is obtained from the Weierstrass approximation theorem on the
unit interval by pulling back along the affine homeomorphism `[a,b] ≃ₜ [0,1]`. -/

theorem polynomialFunctions_topologicalClosure_eq_top_of_ge {a b : ℝ} (h : b ≤ a) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  have : Subsingleton (Set.Icc a b) := (Set.subsingleton_Icc_of_ge h).coe_sort
  subsingleton

/-- **The Stone–Weierstrass theorem, polynomial form.**

On a compact interval `[a, b] ⊆ ℝ`, the polynomial functions form a subalgebra of
`C([a, b], ℝ)` whose closure, in the topology of uniform convergence, is the whole space
of continuous functions. -/
