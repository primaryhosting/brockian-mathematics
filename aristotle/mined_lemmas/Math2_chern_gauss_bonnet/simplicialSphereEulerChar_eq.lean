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

theorem simplicialSphereEulerChar_eq (m : ℕ) : simplicialSphereEulerChar m = 2 := by
  have h := Int.alternating_sum_range_choose (n := 2 * m + 2)
  rw [Finset.sum_range_succ', Finset.sum_range_succ] at h
  simp only [Nat.choose_zero_right, Nat.choose_self, pow_succ, pow_mul, Nat.cast_one, mul_one,
    if_neg (by omega : ¬(2 * m + 2 = 0))] at h
  have hneg : ∑ x ∈ Finset.range (2 * m + 1), (-1 : ℤ) ^ x * -1 * ((2 * m + 2).choose (x + 1) : ℤ)
      = -∑ k ∈ Finset.range (2 * m + 1), (-1 : ℤ) ^ k * ((2 * m + 2).choose (k + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hneg] at h
  norm_num at h
  simp only [simplicialSphereEulerChar]
  linarith

/-! ## Chern–Gauss–Bonnet for the round spheres -/

/-- **The Chern–Gauss–Bonnet theorem for the even-dimensional round spheres.**

For the closed even-dimensional manifold `S^{2m}` with its round metric of constant curvature
one, the Euler form is `(2π)^{-m} Pf(Ω)`; by `Math2.spherePfaffian_eq` its density with respect
to the Riemannian volume is the constant `(2m)!/(2^m m!) / (2π)^m`.  The theorem states that the
integral of the Euler form over `S^{2m}` — that constant times the total surface measure
`Math2.sphereArea m` — equals the Euler characteristic of `S^{2m}`, computed here as the Euler
characteristic of its triangulation by the boundary of the `(2m+1)`-simplex. -/
