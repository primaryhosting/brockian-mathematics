/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

/-! ## Basic vector algebra in `ℝ³` -/

/-- Euclidean three-space, as a triple of reals. -/
abbrev R3 := ℝ × ℝ × ℝ

/-- The standard inner product on `ℝ³`. -/

lemma torus_pd22 (R r : ℝ) :
    pd2 (pd2 (torusParam R r)) =
      fun u v => (-((R + r * Real.cos u) * Real.cos v), -((R + r * Real.cos u) * Real.sin v),
        0) := by
  rw [torus_pd2]
  funext u v
  simp [pd2, mul_comm]

/-! ### The area element and mean curvature of the torus -/

/-- Positivity of the distance to the axis of revolution. -/
