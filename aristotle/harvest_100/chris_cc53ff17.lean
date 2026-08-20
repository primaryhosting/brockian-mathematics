/-
# Banach Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.banach_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Analysis

/-- **Banach fixed-point theorem** (contraction mapping theorem):
a contraction `f` with constant `K < 1` on a nonempty complete metric space has a fixed point,
namely `ContractingWith.fixedPoint f hf`, and this fixed point is unique.
The existence part is `ContractingWith.fixedPoint_isFixedPt` and uniqueness is
`ContractingWith.fixedPoint_unique` in Mathlib. -/
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {f : X → X} (hf : ContractingWith K f) :
    f (ContractingWith.fixedPoint f hf) = ContractingWith.fixedPoint f hf ∧
      ∀ y : X, f y = y → y = ContractingWith.fixedPoint f hf := by
  refine ⟨hf.fixedPoint_isFixedPt, fun y hy => ?_⟩
  exact hf.fixedPoint_unique hy

/-- The plain existence statement: a contraction on a nonempty complete metric space
has a fixed point. -/
theorem banach_fixed_point_exists {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {f : X → X} (hf : ContractingWith K f) :
    ∃ x : X, f x = x :=
  ⟨ContractingWith.fixedPoint f hf, hf.fixedPoint_isFixedPt⟩

end Analysis

