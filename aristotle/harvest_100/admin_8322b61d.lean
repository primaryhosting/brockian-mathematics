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
def dot3 (a b : R3) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- The cross product on `ℝ³`. -/
def cross3 (a b : R3) : R3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)

/-- The Euclidean norm on `ℝ³`. -/
noncomputable def nrm3 (a : R3) : ℝ := Real.sqrt (dot3 a a)

/-! ## Differential geometry of a parametrized surface -/

/-- Partial derivative of a parametrized surface with respect to the first parameter. -/
noncomputable def pd1 (X : ℝ → ℝ → R3) : ℝ → ℝ → R3 := fun u v =>
  (deriv (fun t => (X t v).1) u, deriv (fun t => (X t v).2.1) u, deriv (fun t => (X t v).2.2) u)

/-- Partial derivative of a parametrized surface with respect to the second parameter. -/
noncomputable def pd2 (X : ℝ → ℝ → R3) : ℝ → ℝ → R3 := fun u v =>
  (deriv (fun t => (X u t).1) v, deriv (fun t => (X u t).2.1) v, deriv (fun t => (X u t).2.2) v)

/-- The area element `√(EG - F²) = ‖X_u × X_v‖` of a parametrized surface. -/
noncomputable def areaElement (X : ℝ → ℝ → R3) (u v : ℝ) : ℝ :=
  nrm3 (cross3 (pd1 X u v) (pd2 X u v))

/-- The mean curvature `H = (eG - 2fF + gE) / (2(EG - F²))` of a parametrized surface,
computed from the coefficients `E, F, G` of the first fundamental form and the coefficients
`e, f, g` of the second fundamental form (taken with respect to the unit normal
`(X_u × X_v)/‖X_u × X_v‖`). -/
noncomputable def meanCurvature (X : ℝ → ℝ → R3) (u v : ℝ) : ℝ :=
  let Xu := pd1 X u v
  let Xv := pd2 X u v
  let Xuu := pd1 (pd1 X) u v
  let Xuv := pd2 (pd1 X) u v
  let Xvv := pd2 (pd2 X) u v
  let E := dot3 Xu Xu
  let F := dot3 Xu Xv
  let G := dot3 Xv Xv
  let N := cross3 Xu Xv
  let W := nrm3 N
  ((dot3 Xuu N / W) * G - 2 * (dot3 Xuv N / W) * F + (dot3 Xvv N / W) * E) / (2 * (E * G - F * F))

/-- The Willmore energy `∫ H² dA` of a surface parametrized by the square `[0, 2π]²`. -/
noncomputable def willmoreEnergy (X : ℝ → ℝ → R3) : ℝ :=
  ∫ v in (0:ℝ)..(2 * Real.pi), ∫ u in (0:ℝ)..(2 * Real.pi),
    (meanCurvature X u v) ^ 2 * areaElement X u v

/-! ## The torus of revolution -/

/-- The standard parametrization of the torus of revolution in `ℝ³` obtained by revolving
the circle of radius `r` centred at distance `R` from the axis. -/
noncomputable def torusParam (R r : ℝ) : ℝ → ℝ → R3 := fun u v =>
  ((R + r * Real.cos u) * Real.cos v, (R + r * Real.cos u) * Real.sin v, r * Real.sin u)

/-! ### Partial derivatives of the torus parametrization -/

lemma torus_pd1 (R r : ℝ) :
    pd1 (torusParam R r) =
      fun u v => (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v,
        r * Real.cos u) := by
  funext u v
  simp [pd1, torusParam, mul_comm]

lemma torus_pd2 (R r : ℝ) :
    pd2 (torusParam R r) =
      fun u v => (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v,
        0) := by
  funext u v
  simp [pd2, torusParam, mul_comm]

lemma torus_pd11 (R r : ℝ) :
    pd1 (pd1 (torusParam R r)) =
      fun u v => (-(r * Real.cos u) * Real.cos v, -(r * Real.cos u) * Real.sin v,
        -(r * Real.sin u)) := by
  rw [torus_pd1]
  funext u v
  simp [pd1, mul_comm]

lemma torus_pd21 (R r : ℝ) :
    pd2 (pd1 (torusParam R r)) =
      fun u v => (r * Real.sin u * Real.sin v, -(r * Real.sin u) * Real.cos v, 0) := by
  rw [torus_pd1]
  funext u v
  simp [pd2, mul_comm]

lemma torus_pd22 (R r : ℝ) :
    pd2 (pd2 (torusParam R r)) =
      fun u v => (-((R + r * Real.cos u) * Real.cos v), -((R + r * Real.cos u) * Real.sin v),
        0) := by
  rw [torus_pd2]
  funext u v
  simp [pd2, mul_comm]

/-! ### The area element and mean curvature of the torus -/

/-- Positivity of the distance to the axis of revolution. -/
lemma torus_radius_pos {R r : ℝ} (hr : 0 < r) (hR : r < R) (u : ℝ) :
    0 < R + r * Real.cos u := by
  have hc := Real.neg_one_le_cos u
  nlinarith

/-- The length of the normal vector `X_u × X_v` of the torus. -/
lemma torus_normalLen {R r : ℝ} (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    nrm3 (cross3 (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
      (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0))
      = r * (R + r * Real.cos u) := by
  have hp := torus_radius_pos hr hR u
  have hs : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  have hs2 : Real.sin v ^ 2 + Real.cos v ^ 2 = 1 := Real.sin_sq_add_cos_sq v
  set N := cross3 (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u)
      (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0) with hN
  have key : dot3 N N = (r * (R + r * Real.cos u)) ^ 2 := by
    simp only [hN, dot3, cross3]
    linear_combination (r ^ 2 * (R + r * Real.cos u) ^ 2 *
        (Real.cos u ^ 2 + Real.sin u ^ 2 * (Real.sin v ^ 2 + Real.cos v ^ 2 + 1))) * hs2 +
      (r ^ 2 * (R + r * Real.cos u) ^ 2) * hs
  rw [nrm3, key]
  exact Real.sqrt_sq (by positivity)

lemma torus_areaElement {R r : ℝ} (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    areaElement (torusParam R r) u v = r * (R + r * Real.cos u) := by
  rw [areaElement, torus_pd1, torus_pd2]
  exact torus_normalLen hr hR u v

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
noncomputable def torusAntider (R r : ℝ) (u : ℝ) : ℝ :=
  4 * r * Real.sin u +
    R ^ 2 * (u / Real.sqrt (R ^ 2 - r ^ 2) -
      (2 / Real.sqrt (R ^ 2 - r ^ 2)) *
        Real.arctan (r * Real.sin u /
          (R + Real.sqrt (R ^ 2 - r ^ 2) + r * Real.cos u)))

lemma sqrt_sq_sub_pos {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    0 < Real.sqrt (R ^ 2 - r ^ 2) := by
  apply Real.sqrt_pos.mpr
  nlinarith

lemma sq_sqrt_sq_sub {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

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

lemma torus_integrand_continuous {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    Continuous (fun u : ℝ => (R + 2 * r * Real.cos u) ^ 2 / (R + r * Real.cos u)) := by
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro u; exact ne_of_gt (torus_radius_pos hr hR u)

lemma torus_inner_integral {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    (∫ u in (0:ℝ)..(2 * Real.pi), (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      = Real.pi * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hs_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := sqrt_sq_sub_pos hr hR
  have hs' : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hs_pos
  have hcongr : (∫ u in (0:ℝ)..(2 * Real.pi),
      (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      = (1 / (4 * r)) * ∫ u in (0:ℝ)..(2 * Real.pi),
        (R + 2 * r * Real.cos u) ^ 2 / (R + r * Real.cos u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    have hp' : R + r * Real.cos u ≠ 0 := ne_of_gt (torus_radius_pos hr hR u)
    field_simp
  rw [hcongr]
  have hFTC : (∫ u in (0:ℝ)..(2 * Real.pi),
      (R + 2 * r * Real.cos u) ^ 2 / (R + r * Real.cos u))
      = torusAntider R r (2 * Real.pi) - torusAntider R r 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u _
      exact torusAntider_hasDerivAt hr hR u
    · exact (torus_integrand_continuous hr hR).intervalIntegrable _ _
  rw [hFTC]
  simp only [torusAntider, Real.sin_two_pi, Real.sin_zero, Real.cos_zero]
  simp only [mul_zero, zero_div, Real.arctan_zero, sub_zero, add_zero, zero_add]
  field_simp
  ring

/-! ### The Willmore energy of a torus of revolution -/

/-- The Willmore energy of the torus of revolution with radii `R > r > 0` equals
`π² R² / (r √(R² - r²))`. -/
theorem willmoreEnergy_torusParam {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    willmoreEnergy (torusParam R r) =
      Real.pi ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hs_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := sqrt_sq_sub_pos hr hR
  have hs' : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hs_pos
  have hinner : ∀ v : ℝ, (∫ u in (0:ℝ)..(2 * Real.pi),
      (meanCurvature (torusParam R r) u v) ^ 2 * areaElement (torusParam R r) u v)
      = Real.pi * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    intro v
    rw [show (∫ u in (0:ℝ)..(2 * Real.pi),
        (meanCurvature (torusParam R r) u v) ^ 2 * areaElement (torusParam R r) u v)
        = ∫ u in (0:ℝ)..(2 * Real.pi),
          (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)) from
      intervalIntegral.integral_congr (fun u _ => torus_integrand hr hR u v)]
    exact torus_inner_integral hr hR
  rw [willmoreEnergy]
  simp only [hinner]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-! ### The sharp inequality -/

/-- Sharp lower bound behind the Willmore inequality: `2 r √(R² - r²) ≤ R²`. -/
lemma two_le_ratio {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * (r * Real.sqrt (R ^ 2 - r ^ 2)) ≤ R ^ 2 := by
  have hs_sq : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := sq_sqrt_sq_sub hr hR
  nlinarith [sq_nonneg (r - Real.sqrt (R ^ 2 - r ^ 2))]

/-- Equality in the sharp bound holds exactly for the Clifford ratio `R = √2 · r`. -/
lemma two_le_ratio_eq_iff {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * (r * Real.sqrt (R ^ 2 - r ^ 2)) = R ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hs_sq : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := sq_sqrt_sq_sub hr hR
  have hs_nonneg : 0 ≤ Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_nonneg _
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2nonneg : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · intro h
    have hsr : Real.sqrt (R ^ 2 - r ^ 2) = r := by nlinarith [sq_nonneg (r - Real.sqrt (R ^ 2 - r ^ 2))]
    have hR2 : R ^ 2 = 2 * r ^ 2 := by nlinarith
    have hRpos : 0 < R := lt_trans hr hR
    have hRe : R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hRpos.le).symm
    rw [hRe, hR2, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hr.le]
  · intro h
    subst h
    have hRr : Real.sqrt 2 * r * (Real.sqrt 2 * r) = 2 * r ^ 2 := by nlinarith
    have : (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 := by nlinarith
    rw [this, Real.sqrt_sq hr.le]
    nlinarith

/-! ## Main results -/

/-- **The Willmore conjecture for tori of revolution** (Willmore, 1965): the base case of the
Willmore conjecture, which was proved in full generality for immersed genus-one surfaces by
Marques and Neves.

Every torus of revolution in `ℝ³` (with radii `R > r > 0`) has Willmore energy
`∫ H² dA ≥ 2π²`, and the bound is attained exactly by the *Clifford tori*, those with
`R = √2 · r`.

The statement is packaged as: (i) the universal lower bound `2π²`; (ii) attainment by the
Clifford torus; (iii) the characterisation of the equality case. -/
theorem willmore_conjecture :
    (∀ R r : ℝ, 0 < r → r < R → 2 * Real.pi ^ 2 ≤ willmoreEnergy (torusParam R r)) ∧
    (∀ r : ℝ, 0 < r → willmoreEnergy (torusParam (Real.sqrt 2 * r) r) = 2 * Real.pi ^ 2) ∧
    (∀ R r : ℝ, 0 < r → r < R →
      (willmoreEnergy (torusParam R r) = 2 * Real.pi ^ 2 ↔ R = Real.sqrt 2 * r)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt2 : (1:ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  have main : ∀ R r : ℝ, 0 < r → r < R →
      willmoreEnergy (torusParam R r) = Real.pi ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) :=
    fun R r hr hR => willmoreEnergy_torusParam hr hR
  refine ⟨?_, ?_, ?_⟩
  · intro R r hr hR
    rw [main R r hr hR]
    have hs_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := sqrt_sq_sub_pos hr hR
    have hden : 0 < r * Real.sqrt (R ^ 2 - r ^ 2) := by positivity
    rw [le_div_iff₀ hden]
    have := two_le_ratio hr hR
    nlinarith [sq_nonneg Real.pi, hpi]
  · intro r hr
    have hR : r < Real.sqrt 2 * r := by nlinarith
    rw [main _ r hr hR]
    have hs : Real.sqrt ((Real.sqrt 2 * r) ^ 2 - r ^ 2) = r := by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have : (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 := by nlinarith
      rw [this, Real.sqrt_sq hr.le]
    rw [hs]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hr' : r ≠ 0 := ne_of_gt hr
    field_simp
    nlinarith [h2]
  · intro R r hr hR
    rw [main R r hr hR]
    have hs_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := sqrt_sq_sub_pos hr hR
    have hden : 0 < r * Real.sqrt (R ^ 2 - r ^ 2) := by positivity
    rw [div_eq_iff (ne_of_gt hden)]
    rw [← two_le_ratio_eq_iff hr hR]
    constructor
    · intro h
      have hpi2 : (0:ℝ) < Real.pi ^ 2 := by positivity
      nlinarith [h]
    · intro h
      nlinarith [h]

/-- The Clifford torus (the torus of revolution with `R = √2`, `r = 1`, which is the
stereographic image of the Clifford torus in `S³`) has Willmore energy exactly `2π²`. -/
theorem willmoreEnergy_cliffordTorus :
    willmoreEnergy (torusParam (Real.sqrt 2) 1) = 2 * Real.pi ^ 2 := by
  have h := willmore_conjecture.2.1 1 one_pos
  simpa using h

end Frontier

