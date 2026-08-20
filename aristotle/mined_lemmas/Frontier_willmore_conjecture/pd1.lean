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

noncomputable def pd1 (X : ℝ → ℝ → R3) : ℝ → ℝ → R3 := fun u v =>
  (deriv (fun t => (X t v).1) u, deriv (fun t => (X t v).2.1) u, deriv (fun t => (X t v).2.2) u)

/-- Partial derivative of a parametrized surface with respect to the second parameter. -/
