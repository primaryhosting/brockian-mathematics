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

lemma torusAntider_hasDerivAt {R r : ℝ} (hr : 0 < r) (hR : r < R) (u : ℝ) :
    HasDerivAt (torusAntider R r)
      ((R + 2 * r * Real.cos u) ^ 2 / (R + r * Real.cos u)) u := by
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs_def
  have hs_pos : 0 < s := sqrt_sq_sub_pos hr hR
  have hs_sq : s ^ 2 = R ^ 2 - r ^ 2 := sq_sqrt_sq_sub hr hR
  have hp := torus_radius_pos hr hR u
  have hD : 0 < R + s + r * Real.cos u := by linarith
  have htrig : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  -- derivative of numerator and denominator of the arctan argument
  have hnum : HasDerivAt (fun t : ℝ => r * Real.sin t) (r * Real.cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul r
  have hden : HasDerivAt (fun t : ℝ => R + s + r * Real.cos t) (-(r * Real.sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add (R + s)
  have hquot : HasDerivAt (fun t : ℝ => r * Real.sin t / (R + s + r * Real.cos t))
      ((r * Real.cos u * (R + s + r * Real.cos u) - r * Real.sin u * (-(r * Real.sin u))) /
        (R + s + r * Real.cos u) ^ 2) u := hnum.div hden (ne_of_gt hD)
  have harctan : HasDerivAt
      (fun t : ℝ => Real.arctan (r * Real.sin t / (R + s + r * Real.cos t)))
      ((1 / (1 + (r * Real.sin u / (R + s + r * Real.cos u)) ^ 2)) *
        ((r * Real.cos u * (R + s + r * Real.cos u) - r * Real.sin u * (-(r * Real.sin u))) /
          (R + s + r * Real.cos u) ^ 2)) u :=
    (Real.hasDerivAt_arctan _).comp u hquot
  have hlin : HasDerivAt (fun t : ℝ => t / s) (1 / s) u := by
    simpa using (hasDerivAt_id u).div_const s
  have hsin : HasDerivAt (fun t : ℝ => 4 * r * Real.sin t) (4 * r * Real.cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul (4 * r)
  have htot : HasDerivAt (torusAntider R r)
      (4 * r * Real.cos u +
        R ^ 2 * (1 / s - (2 / s) *
          ((1 / (1 + (r * Real.sin u / (R + s + r * Real.cos u)) ^ 2)) *
            ((r * Real.cos u * (R + s + r * Real.cos u) -
              r * Real.sin u * (-(r * Real.sin u))) /
              (R + s + r * Real.cos u) ^ 2)))) u := by
    have := hsin.add (((hlin.sub (harctan.const_mul (2 / s)))).const_mul (R ^ 2))
    simpa [torusAntider, hs_def] using this
  -- simplify the derivative
  have hkey : (1 / (1 + (r * Real.sin u / (R + s + r * Real.cos u)) ^ 2)) *
      ((r * Real.cos u * (R + s + r * Real.cos u) - r * Real.sin u * (-(r * Real.sin u))) /
        (R + s + r * Real.cos u) ^ 2)
      = (r * (R + s) * Real.cos u + r ^ 2) / (2 * (R + s) * (R + r * Real.cos u)) := by
    have hD' : R + s + r * Real.cos u ≠ 0 := ne_of_gt hD
    have hsum : (R + s + r * Real.cos u) ^ 2 + (r * Real.sin u) ^ 2
        = 2 * (R + s) * (R + r * Real.cos u) := by
      linear_combination (r ^ 2) * htrig + hs_sq
    have h1 : 1 + (r * Real.sin u / (R + s + r * Real.cos u)) ^ 2
        = (2 * (R + s) * (R + r * Real.cos u)) / (R + s + r * Real.cos u) ^ 2 := by
      field_simp
      linear_combination hsum
    have hnum2 : r * Real.cos u * (R + s + r * Real.cos u) - r * Real.sin u * (-(r * Real.sin u))
        = r * (R + s) * Real.cos u + r ^ 2 := by
      linear_combination (r ^ 2) * htrig
    rw [hnum2, h1]
    have hpos2 : (0:ℝ) < 2 * (R + s) * (R + r * Real.cos u) :=
      mul_pos (by linarith) hp
    have hne2 : (2 * (R + s) * (R + r * Real.cos u)) ≠ 0 := ne_of_gt hpos2
    field_simp
  rw [hkey] at htot
  have hfinal : 4 * r * Real.cos u +
      R ^ 2 * (1 / s - (2 / s) *
        ((r * (R + s) * Real.cos u + r ^ 2) / (2 * (R + s) * (R + r * Real.cos u))))
      = (R + 2 * r * Real.cos u) ^ 2 / (R + r * Real.cos u) := by
    have hs' : s ≠ 0 := ne_of_gt hs_pos
    have hRs : R + s ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < R + s)
    have hp' : R + r * Real.cos u ≠ 0 := ne_of_gt hp
    have hsplit : (1:ℝ) / s - (2 / s) *
        ((r * (R + s) * Real.cos u + r ^ 2) / (2 * (R + s) * (R + r * Real.cos u)))
        = (2 * (R + s) * (R + r * Real.cos u) - 2 * (r * (R + s) * Real.cos u + r ^ 2)) /
          (s * (2 * (R + s) * (R + r * Real.cos u))) := by
      field_simp
    have hnumer : 2 * (R + s) * (R + r * Real.cos u) - 2 * (r * (R + s) * Real.cos u + r ^ 2)
        = 2 * s * (R + s) := by
      linear_combination (-2 : ℝ) * hs_sq
    have hstep : (1:ℝ) / s - (2 / s) *
        ((r * (R + s) * Real.cos u + r ^ 2) / (2 * (R + s) * (R + r * Real.cos u)))
        = 1 / (R + r * Real.cos u) := by
      rw [hsplit, hnumer]
      field_simp
    rw [hstep]
    field_simp
    ring
  rw [hfinal] at htot
  exact htot

