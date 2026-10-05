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

/-!
# Banach Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.banach_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Analysis

/-- **Banach fixed-point (contraction mapping) theorem.**
If `X` is a nonempty complete metric space and `f : X → X` is a contraction with
constant `K`, then `ContractingWith.fixedPoint` is a fixed point of `f`, and `f`
has a unique fixed point. -/
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {f : X → X} (hf : ContractingWith K f) :
    f (hf.fixedPoint f) = hf.fixedPoint f ∧
      ∃ x : X, f x = x ∧ ∀ y : X, f y = y → y = x := by
  have h : f (hf.fixedPoint f) = hf.fixedPoint f := hf.fixedPoint_isFixedPt
  exact ⟨h, hf.fixedPoint f, h, fun _ hy => hf.fixedPoint_unique hy⟩

#print axioms Analysis.banach_fixed_point

end Analysis

