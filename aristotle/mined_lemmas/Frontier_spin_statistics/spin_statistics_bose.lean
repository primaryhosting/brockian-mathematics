import Mathlib
/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
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

/-! ## Minkowski spacetime -/

/-- Four dimensional Minkowski spacetime, as coordinate tuples `(x⁰, x¹, x², x³)`. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- The Minkowski quadratic form `x·x = (x⁰)² - (x¹)² - (x²)² - (x³)²`
(mostly-minus signature). -/

theorem spin_statistics_bose (F : RelativisticQuantumField) (h : Even F.twoSpin) :
    F.stat = 1 := by
  rw [spin_statistics F]; exact h.neg_one_pow

/-- Half-integer spin fields are fermions. -/
