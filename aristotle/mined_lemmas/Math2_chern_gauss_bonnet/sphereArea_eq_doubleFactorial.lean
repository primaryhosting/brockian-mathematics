/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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

namespace Math2

open Finset MeasureTheory Metric Module Real Set

/-! ## The Pfaffian of the curvature form of the unit round sphere -/

section Pfaffian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First index of the `i`-th pair `(2i, 2i+1)`. -/

theorem sphereArea_eq_doubleFactorial (m : ℕ) :
    sphereArea m = (2 * m + 1) * (π ^ m * 2 ^ (m + 1) / ((2 * m + 1)‼ : ℕ)) := by
  rw [sphereArea, Measure.toSphere_real_apply_univ]
  have hrank : finrank ℝ (EuclideanSpace ℝ (Fin (2 * m + 1))) = 2 * m + 1 := by simp
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_odd (k := m) (by simp) 0 1, hrank]
  have hpos : (0 : ℝ) ≤ π ^ m * 2 ^ (m + 1) / ((2 * m + 1)‼ : ℕ) := by positivity
  rw [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal hpos]
  push_cast
  ring

