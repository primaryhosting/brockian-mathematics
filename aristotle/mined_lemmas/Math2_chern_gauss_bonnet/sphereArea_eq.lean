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

theorem sphereArea_eq (m : ℕ) :
    sphereArea m = 2 ^ (2 * m + 1) * π ^ m * (m)! / (2 * m)! := by
  have hcast : ((2 * m + 1)‼ : ℝ) * (2 ^ m * (m)!) = (2 * m + 1) * ((2 * m)! : ℕ) := by
    have h : ((2 * m + 1)‼ * (2 ^ m * (m)!) : ℕ) = ((2 * m + 1) * (2 * m)! : ℕ) := by
      rw [doubleFactorial_mul, Nat.factorial_succ]
    exact_mod_cast h
  rw [sphereArea_eq_doubleFactorial, mul_div_assoc',
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(π ^ m * 2 ^ (m + 1))) * hcast

/-! ## The Euler characteristic of a simplicial `2m`-sphere -/

/-- The Euler characteristic of the boundary complex of the `(2m+1)`-simplex, a triangulation
of the `2m`-sphere: the alternating sum of the numbers of `k`-dimensional faces. -/
