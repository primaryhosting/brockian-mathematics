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

lemma torus_meanCurvature {R r : ℝ} (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    meanCurvature (torusParam R r) u v =
      (R + 2 * r * Real.cos u) / (2 * r * (R + r * Real.cos u)) := by
  have hp := torus_radius_pos hr hR u
  have hs : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  have hs2 : Real.sin v ^ 2 + Real.cos v ^ 2 = 1 := Real.sin_sq_add_cos_sq v
  simp only [meanCurvature]
  rw [torus_pd11 R r, torus_pd21 R r, torus_pd22 R r, torus_pd1 R r, torus_pd2 R r]
  rw [torus_normalLen hr hR]
  have hE : dot3 (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
      (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
      = r ^ 2 := by
    simp only [dot3]
    linear_combination (r ^ 2 * Real.sin u ^ 2) * hs2 + r ^ 2 * hs
  have hF : dot3 (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
      (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0)
      = 0 := by
    simp only [dot3]; ring
  have hG : dot3 (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0)
      (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0)
      = (R + r * Real.cos u) ^ 2 := by
    simp only [dot3]
    linear_combination ((R + r * Real.cos u) ^ 2) * hs2
  have he : dot3 (-(r * Real.cos u) * Real.cos v, -(r * Real.cos u) * Real.sin v,
        -(r * Real.sin u))
      (cross3 (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
        (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0))
      = r ^ 2 * (R + r * Real.cos u) := by
    simp only [dot3, cross3]
    linear_combination (r ^ 2 * (R + r * Real.cos u) * (Real.sin u ^ 2 + Real.cos u ^ 2)) * hs2 +
      (r ^ 2 * (R + r * Real.cos u)) * hs
  have hf : dot3 (r * Real.sin u * Real.sin v, -(r * Real.sin u) * Real.cos v, 0)
      (cross3 (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
        (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0))
      = 0 := by
    simp only [dot3, cross3]; ring
  have hg : dot3 (-((R + r * Real.cos u) * Real.cos v), -((R + r * Real.cos u) * Real.sin v), 0)
      (cross3 (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
        (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0))
      = r * Real.cos u * (R + r * Real.cos u) ^ 2 := by
    simp only [dot3, cross3]
    linear_combination (r * Real.cos u * (R + r * Real.cos u) ^ 2) * hs2
  rw [hE, hF, hG, he, hf, hg]
  have hr' : r ≠ 0 := ne_of_gt hr
  have hp' : R + r * Real.cos u ≠ 0 := ne_of_gt hp
  field_simp
  ring

