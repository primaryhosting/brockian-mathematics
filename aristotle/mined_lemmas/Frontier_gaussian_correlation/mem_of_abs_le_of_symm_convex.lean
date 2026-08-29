/-
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory ProbabilityTheory

/-- The standard (centred, identity covariance) Gaussian measure on `Fin n → ℝ`,
built as the `n`-fold product of the real standard Gaussian. -/

theorem mem_of_abs_le_of_symm_convex {S : Set (Fin 1 → ℝ)} (hconv : Convex ℝ S)
    (hsymm : ∀ x ∈ S, -x ∈ S) {x y : Fin 1 → ℝ} (hx : x ∈ S) (hxy : |y 0| ≤ |x 0|) :
    y ∈ S := by
  by_cases hx0 : x 0 = 0
  · have hy0 : y 0 = 0 := by
      have : |y 0| ≤ 0 := by simpa [hx0] using hxy
      simpa using abs_nonpos_iff.mp this
    have : y = x := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [hy0, hx0]
    rw [this]; exact hx
  · set a : ℝ := x 0 with ha
    set b : ℝ := y 0 with hb
    have hxa : |b| ≤ |a| := hxy
    have habs : |b / a| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hx0)).mpr hxa
    set t : ℝ := (1 + b / a) / 2 with ht
    have h1 : (0:ℝ) ≤ t := by
      have : -1 ≤ b / a := (abs_le.mp habs).1
      simp only [ht]
      linarith
    have h2 : (0:ℝ) ≤ 1 - t := by
      have : b / a ≤ 1 := (abs_le.mp habs).2
      simp only [ht]
      linarith
    have hsum : t + (1 - t) = 1 := by ring
    have hmem : t • x + (1 - t) • (-x) ∈ S := hconv hx (hsymm x hx) h1 h2 hsum
    have heq : t • x + (1 - t) • (-x) = y := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      rw [← ha, ← hb, ht]
      field_simp
      ring
    rw [← heq]; exact hmem

/-- In dimension one, two origin-symmetric convex sets are always nested. -/
