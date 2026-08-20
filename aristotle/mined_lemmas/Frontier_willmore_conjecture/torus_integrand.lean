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

lemma torus_integrand {R r : ℝ} (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (meanCurvature (torusParam R r) u v) ^ 2 * areaElement (torusParam R r) u v =
      (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)) := by
  have hp := torus_radius_pos hr hR u
  have hr' : r ≠ 0 := ne_of_gt hr
  have hp' : R + r * Real.cos u ≠ 0 := ne_of_gt hp
  rw [torus_meanCurvature hr hR, torus_areaElement hr hR]
  field_simp
  ring

/-! ### The key integral -/

/-- A globally smooth antiderivative of `u ↦ (R + 2r cos u)² / (R + r cos u)`. -/
