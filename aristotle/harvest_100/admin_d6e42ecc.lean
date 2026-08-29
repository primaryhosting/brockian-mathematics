/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- therefore a plain block comment, and is repeated verbatim as a module docstring below.)

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

set_option grind.warning false

namespace Frontier

open Real intervalIntegral

/-! ## Vector algebra in `ℝ³`

We use `ℝ × ℝ × ℝ` as a model of `ℝ³` together with explicitly defined dot product,
cross product and Euclidean norm.  (The ambient `Prod` norm of Mathlib is the sup norm,
so we never use `‖·‖`; note that the notion of (Fréchet/one-variable) derivative does
not depend on the choice of an equivalent norm, so `deriv` below is the usual derivative
of an `ℝ³`-valued function.) -/

/-- Euclidean dot product on `ℝ³`. -/
def dot3 (a b : ℝ × ℝ × ℝ) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- Cross product on `ℝ³`. -/
def cross3 (a b : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)

/-- Euclidean norm on `ℝ³`. -/
noncomputable def nrm3 (a : ℝ × ℝ × ℝ) : ℝ := Real.sqrt (dot3 a a)

/-! ## The torus of revolution

`torusMap R r` is the standard parametrization of the torus of revolution obtained by
rotating the circle of radius `r` centred at distance `R` from the axis. -/

/-- The standard parametrization of the torus of revolution with radii `R > r > 0`. -/
noncomputable def torusMap (R r : ℝ) (u v : ℝ) : ℝ × ℝ × ℝ :=
  ((R + r * cos u) * cos v, (R + r * cos u) * sin v, r * sin u)

/-- First partial derivative of the parametrization in the `u` (meridian) direction. -/
noncomputable def Xu (R r : ℝ) (u v : ℝ) : ℝ × ℝ × ℝ := deriv (fun t => torusMap R r t v) u

/-- First partial derivative of the parametrization in the `v` (rotation) direction. -/
noncomputable def Xv (R r : ℝ) (u v : ℝ) : ℝ × ℝ × ℝ := deriv (fun t => torusMap R r u t) v

/-- Second partial derivative `∂²X/∂u²`. -/
noncomputable def Xuu (R r : ℝ) (u v : ℝ) : ℝ × ℝ × ℝ := deriv (fun t => Xu R r t v) u

/-- Mixed second partial derivative `∂²X/∂u∂v`. -/
noncomputable def Xuv (R r : ℝ) (u v : ℝ) : ℝ × ℝ × ℝ := deriv (fun t => Xu R r u t) v

/-- Second partial derivative `∂²X/∂v²`. -/
noncomputable def Xvv (R r : ℝ) (u v : ℝ) : ℝ × ℝ × ℝ := deriv (fun t => Xv R r u t) v

lemma hasDerivAt_torusMap_u (R r u v : ℝ) :
    HasDerivAt (fun t => torusMap R r t v)
      (-(r * sin u) * cos v, -(r * sin u) * sin v, r * cos u) u := by
  have hb : HasDerivAt (fun t : ℝ => R + r * cos t) (-(r * sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add R
  have h1 : HasDerivAt (fun t : ℝ => (R + r * cos t) * cos v) (-(r * sin u) * cos v) u :=
    hb.mul_const _
  have h2 : HasDerivAt (fun t : ℝ => (R + r * cos t) * sin v) (-(r * sin u) * sin v) u :=
    hb.mul_const _
  have h3 : HasDerivAt (fun t : ℝ => r * sin t) (r * cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul r
  exact h1.prodMk (h2.prodMk h3)

lemma hasDerivAt_torusMap_v (R r u v : ℝ) :
    HasDerivAt (fun t => torusMap R r u t)
      (-((R + r * cos u) * sin v), (R + r * cos u) * cos v, 0) v := by
  have h1 : HasDerivAt (fun t : ℝ => (R + r * cos u) * cos t) (-((R + r * cos u) * sin v)) v := by
    simpa [mul_comm] using ((Real.hasDerivAt_cos v).const_mul (R + r * cos u))
  have h2 : HasDerivAt (fun t : ℝ => (R + r * cos u) * sin t) ((R + r * cos u) * cos v) v := by
    simpa using ((Real.hasDerivAt_sin v).const_mul (R + r * cos u))
  have h3 : HasDerivAt (fun _ : ℝ => r * sin u) (0 : ℝ) v := hasDerivAt_const _ _
  exact h1.prodMk (h2.prodMk h3)

lemma Xu_eq (R r u v : ℝ) :
    Xu R r u v = (-(r * sin u) * cos v, -(r * sin u) * sin v, r * cos u) :=
  (hasDerivAt_torusMap_u R r u v).deriv

lemma Xv_eq (R r u v : ℝ) :
    Xv R r u v = (-((R + r * cos u) * sin v), (R + r * cos u) * cos v, 0) :=
  (hasDerivAt_torusMap_v R r u v).deriv

lemma Xuu_eq (R r u v : ℝ) :
    Xuu R r u v = (-(r * cos u) * cos v, -(r * cos u) * sin v, -(r * sin u)) := by
  have h1 : HasDerivAt (fun t : ℝ => -(r * sin t) * cos v) (-(r * cos u) * cos v) u := by
    have : HasDerivAt (fun t : ℝ => -(r * sin t)) (-(r * cos u)) u := by
      simpa using ((Real.hasDerivAt_sin u).const_mul r).neg
    exact this.mul_const _
  have h2 : HasDerivAt (fun t : ℝ => -(r * sin t) * sin v) (-(r * cos u) * sin v) u := by
    have : HasDerivAt (fun t : ℝ => -(r * sin t)) (-(r * cos u)) u := by
      simpa using ((Real.hasDerivAt_sin u).const_mul r).neg
    exact this.mul_const _
  have h3 : HasDerivAt (fun t : ℝ => r * cos t) (-(r * sin u)) u := by
    simpa [mul_comm] using ((Real.hasDerivAt_cos u).const_mul r)
  have := (h1.prodMk (h2.prodMk h3)).deriv
  rw [Xuu]
  simpa only [Xu_eq] using this

lemma Xuv_eq (R r u v : ℝ) :
    Xuv R r u v = (r * sin u * sin v, -(r * sin u) * cos v, 0) := by
  have h1 : HasDerivAt (fun t : ℝ => -(r * sin u) * cos t) (r * sin u * sin v) v := by
    simpa [mul_comm] using ((Real.hasDerivAt_cos v).const_mul (-(r * sin u)))
  have h2 : HasDerivAt (fun t : ℝ => -(r * sin u) * sin t) (-(r * sin u) * cos v) v := by
    simpa using ((Real.hasDerivAt_sin v).const_mul (-(r * sin u)))
  have h3 : HasDerivAt (fun _ : ℝ => r * cos u) (0 : ℝ) v := hasDerivAt_const _ _
  have := (h1.prodMk (h2.prodMk h3)).deriv
  rw [Xuv]
  simpa only [Xu_eq] using this

lemma Xvv_eq (R r u v : ℝ) :
    Xvv R r u v = (-((R + r * cos u) * cos v), -((R + r * cos u) * sin v), 0) := by
  have h1 : HasDerivAt (fun t : ℝ => -((R + r * cos u) * sin t)) (-((R + r * cos u) * cos v)) v := by
    simpa using ((Real.hasDerivAt_sin v).const_mul (R + r * cos u)).neg
  have h2 : HasDerivAt (fun t : ℝ => (R + r * cos u) * cos t) (-((R + r * cos u) * sin v)) v := by
    simpa [mul_comm] using ((Real.hasDerivAt_cos v).const_mul (R + r * cos u))
  have h3 : HasDerivAt (fun _ : ℝ => (0:ℝ)) (0 : ℝ) v := hasDerivAt_const _ _
  have := (h1.prodMk (h2.prodMk h3)).deriv
  rw [Xvv]
  simpa only [Xv_eq] using this

/-! ## Fundamental forms -/

/-- Coefficient `E = ⟨X_u, X_u⟩` of the first fundamental form. -/
noncomputable def formE (R r u v : ℝ) : ℝ := dot3 (Xu R r u v) (Xu R r u v)
/-- Coefficient `F = ⟨X_u, X_v⟩` of the first fundamental form. -/
noncomputable def formF (R r u v : ℝ) : ℝ := dot3 (Xu R r u v) (Xv R r u v)
/-- Coefficient `G = ⟨X_v, X_v⟩` of the first fundamental form. -/
noncomputable def formG (R r u v : ℝ) : ℝ := dot3 (Xv R r u v) (Xv R r u v)

/-- The unit normal `(X_u × X_v)/|X_u × X_v|` of the parametrized torus. -/
noncomputable def unitNormal (R r u v : ℝ) : ℝ × ℝ × ℝ :=
  (nrm3 (cross3 (Xu R r u v) (Xv R r u v)))⁻¹ • cross3 (Xu R r u v) (Xv R r u v)

/-- Coefficient `e = ⟨X_uu, N⟩` of the second fundamental form. -/
noncomputable def forme (R r u v : ℝ) : ℝ := dot3 (Xuu R r u v) (unitNormal R r u v)
/-- Coefficient `f = ⟨X_uv, N⟩` of the second fundamental form. -/
noncomputable def formf (R r u v : ℝ) : ℝ := dot3 (Xuv R r u v) (unitNormal R r u v)
/-- Coefficient `g = ⟨X_vv, N⟩` of the second fundamental form. -/
noncomputable def formg (R r u v : ℝ) : ℝ := dot3 (Xvv R r u v) (unitNormal R r u v)

/-- The mean curvature `H = (eG - 2fF + gE)/(2(EG - F²))` of the parametrized surface. -/
noncomputable def meanCurv (R r u v : ℝ) : ℝ :=
  (forme R r u v * formG R r u v - 2 * formf R r u v * formF R r u v
      + formg R r u v * formE R r u v) / (2 * (formE R r u v * formG R r u v - formF R r u v ^ 2))

/-- The area element `√(EG - F²)` of the parametrized surface. -/
noncomputable def areaElt (R r u v : ℝ) : ℝ :=
  Real.sqrt (formE R r u v * formG R r u v - formF R r u v ^ 2)

/-! ## Explicit computation of the fundamental forms of the torus -/

lemma radial_pos {R r u : ℝ} (hr : 0 < r) (hR : r < R) : 0 < R + r * cos u := by
  nlinarith [neg_one_le_cos u, cos_le_one u]

lemma cross_Xu_Xv (R r u v : ℝ) :
    cross3 (Xu R r u v) (Xv R r u v) =
      (-(r * (R + r * cos u) * (cos u * cos v)), -(r * (R + r * cos u) * (cos u * sin v)),
        -(r * (R + r * cos u) * sin u)) := by
  have hv := sin_sq_add_cos_sq v
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [cross3, Xu_eq, Xv_eq]; ring
  · simp only [cross3, Xu_eq, Xv_eq]; ring
  · simp only [cross3, Xu_eq, Xv_eq]
    linear_combination (-(r * sin u * (R + r * cos u))) * hv

lemma nrm3_cross {R r u v : ℝ} (hr : 0 < r) (hR : r < R) :
    nrm3 (cross3 (Xu R r u v) (Xv R r u v)) = r * (R + r * cos u) := by
  have hp := radial_pos (u := u) hr hR
  have hpos : 0 < r * (R + r * cos u) := mul_pos hr hp
  have hu := sin_sq_add_cos_sq u
  have hv := sin_sq_add_cos_sq v
  have key : dot3 (cross3 (Xu R r u v) (Xv R r u v)) (cross3 (Xu R r u v) (Xv R r u v))
      = (r * (R + r * cos u)) ^ 2 := by
    simp only [cross_Xu_Xv, dot3]
    linear_combination ((r * (R + r * cos u)) ^ 2 * cos u ^ 2) * hv
      + ((r * (R + r * cos u)) ^ 2) * hu
  rw [nrm3, key, Real.sqrt_sq hpos.le]

lemma unitNormal_eq {R r u v : ℝ} (hr : 0 < r) (hR : r < R) :
    unitNormal R r u v = (-(cos u * cos v), -(cos u * sin v), -sin u) := by
  have hp := radial_pos (u := u) hr hR
  have hne : r * (R + r * cos u) ≠ 0 := ne_of_gt (mul_pos hr hp)
  rw [unitNormal, nrm3_cross hr hR, cross_Xu_Xv]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      field_simp

lemma formE_eq (R r u v : ℝ) : formE R r u v = r ^ 2 := by
  have hu := sin_sq_add_cos_sq u
  have hv := sin_sq_add_cos_sq v
  simp only [formE, dot3, Xu_eq]
  linear_combination (r ^ 2 * sin u ^ 2) * hv + r ^ 2 * hu

lemma formF_eq (R r u v : ℝ) : formF R r u v = 0 := by
  simp only [formF, dot3, Xu_eq, Xv_eq]; ring

lemma formG_eq (R r u v : ℝ) : formG R r u v = (R + r * cos u) ^ 2 := by
  have hv := sin_sq_add_cos_sq v
  simp only [formG, dot3, Xv_eq]
  linear_combination ((R + r * cos u) ^ 2) * hv

lemma forme_eq {R r u v : ℝ} (hr : 0 < r) (hR : r < R) : forme R r u v = r := by
  have hu := sin_sq_add_cos_sq u
  have hv := sin_sq_add_cos_sq v
  simp only [forme, dot3, Xuu_eq, unitNormal_eq hr hR]
  linear_combination (r * cos u ^ 2) * hv + r * hu

lemma formf_eq {R r u v : ℝ} (hr : 0 < r) (hR : r < R) : formf R r u v = 0 := by
  simp only [formf, dot3, Xuv_eq, unitNormal_eq hr hR]; ring

lemma formg_eq {R r u v : ℝ} (hr : 0 < r) (hR : r < R) :
    formg R r u v = (R + r * cos u) * cos u := by
  have hv := sin_sq_add_cos_sq v
  simp only [formg, dot3, Xvv_eq, unitNormal_eq hr hR]
  linear_combination ((R + r * cos u) * cos u) * hv

/-- The classical formula for the mean curvature of a torus of revolution. -/
lemma meanCurv_eq {R r u v : ℝ} (hr : 0 < r) (hR : r < R) :
    meanCurv R r u v = (R + 2 * r * cos u) / (2 * r * (R + r * cos u)) := by
  have hp := radial_pos (u := u) hr hR
  rw [meanCurv, forme_eq hr hR, formf_eq hr hR, formg_eq hr hR, formE_eq, formF_eq, formG_eq]
  have h1 : 2 * (r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2) ≠ 0 := by
    have : (0:ℝ) < 2 * (r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2) := by nlinarith [mul_pos hr hp]
    exact ne_of_gt this
  have h2 : 2 * r * (R + r * cos u) ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  ring

/-- The classical formula for the area element of a torus of revolution. -/
lemma areaElt_eq {R r u v : ℝ} (hr : 0 < r) (hR : r < R) :
    areaElt R r u v = r * (R + r * cos u) := by
  have hp := radial_pos (u := u) hr hR
  rw [areaElt, formE_eq, formF_eq, formG_eq]
  rw [show r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2 = (r * (R + r * cos u)) ^ 2 by ring]
  exact Real.sqrt_sq (mul_pos hr hp).le


/-! ## The Willmore energy of a torus of revolution

We now compute `∫∫ H² dA` over the torus.  The key analytic ingredient is the explicit
antiderivative of `u ↦ 1/(R + r cos u)`. -/

/-- An explicit antiderivative of `u ↦ 1/(R + r cos u)`, globally smooth on `ℝ`. -/
lemma hasDerivAt_willmoreAntideriv {R r : ℝ} (hr : 0 < r) (hR : r < R) (u : ℝ) :
    HasDerivAt (fun t : ℝ =>
        (t - 2 * arctan (r * sin t / (R + Real.sqrt (R ^ 2 - r ^ 2) + r * cos t)))
          / Real.sqrt (R ^ 2 - r ^ 2))
      (1 / (R + r * cos u)) u := by
  have hR0 : 0 < R := lt_trans hr hR
  have hsq : 0 < R ^ 2 - r ^ 2 := by nlinarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (R ^ 2 - r ^ 2) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.mpr hsq
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := hs_def ▸ Real.sq_sqrt hsq.le
  rw [← hs_def]
  have hp : 0 < R + r * cos u := radial_pos hr hR
  have hDpos : 0 < R + s + r * cos u := by linarith
  have hDne : R + s + r * cos u ≠ 0 := ne_of_gt hDpos
  have hRs : (0:ℝ) < R + s := by linarith
  have hN : HasDerivAt (fun t : ℝ => r * sin t) (r * cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul r
  have hDd : HasDerivAt (fun t : ℝ => R + s + r * cos t) (-(r * sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add (R + s)
  have hq := hN.div hDd hDne
  have harc := (hasDerivAt_arctan (r * sin u / (R + s + r * cos u))).comp u hq
  have h1 : HasDerivAt (fun t : ℝ => t) (1:ℝ) u := hasDerivAt_id u
  have hmain := (h1.sub (harc.const_mul 2)).div_const s
  convert hmain using 1
  have hsin := sin_sq_add_cos_sq u
  have h1p : 1 + (r * sin u / (R + s + r * cos u)) ^ 2
      = (2 * (R + s) * (R + r * cos u)) / (R + s + r * cos u) ^ 2 := by
    field_simp
    linear_combination r ^ 2 * hsin + hs2
  have hnum : r * cos u * (R + s + r * cos u) - r * sin u * -(r * sin u)
      = r * ((R + s) * cos u + r) := by linear_combination r ^ 2 * hsin
  rw [h1p, one_div_div, hnum]
  have hprod : (R + s + r * cos u) ^ 2 / (2 * (R + s) * (R + r * cos u))
        * (r * ((R + s) * cos u + r) / (R + s + r * cos u) ^ 2)
      = r * ((R + s) * cos u + r) / (2 * (R + s) * (R + r * cos u)) := by
    field_simp
  rw [hprod, eq_div_iff (ne_of_gt hs)]
  field_simp
  linear_combination hs2

lemma continuous_inv_radial {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    Continuous fun u : ℝ => 1 / (R + r * cos u) :=
  continuous_const.div (by continuity) fun _ => ne_of_gt (radial_pos hr hR)

/-- `∫₀^{2π} du/(R + r cos u) = 2π/√(R² - r²)`. -/
lemma integral_inv_radial {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    ∫ u in (0:ℝ)..(2 * π), 1 / (R + r * cos u) = 2 * π / Real.sqrt (R ^ 2 - r ^ 2) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 2 * π)
    (f := fun t : ℝ => (t - 2 * arctan (r * sin t / (R + Real.sqrt (R ^ 2 - r ^ 2) + r * cos t)))
          / Real.sqrt (R ^ 2 - r ^ 2))
    (f' := fun u : ℝ => 1 / (R + r * cos u))
    (fun x _ => hasDerivAt_willmoreAntideriv hr hR x)
    ((continuous_inv_radial hr hR).intervalIntegrable _ _)
  rw [h]
  simp

/-- Pointwise, `H² · dA = cos u + (R²/4r) · 1/(R + r cos u)`. -/
lemma willmore_integrand_eq {R r : ℝ} (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    meanCurv R r u v ^ 2 * areaElt R r u v
      = cos u + R ^ 2 / (4 * r) * (1 / (R + r * cos u)) := by
  have hp : 0 < R + r * cos u := radial_pos hr hR
  rw [meanCurv_eq hr hR, areaElt_eq hr hR]
  field_simp
  ring

lemma sqrt_sub_pos {R r : ℝ} (hr : 0 < r) (hR : r < R) : 0 < Real.sqrt (R ^ 2 - r ^ 2) := by
  have hR0 : 0 < R := lt_trans hr hR
  exact Real.sqrt_pos.mpr (by nlinarith)

/-- The integral of `H² dA` along a meridian circle. -/
lemma inner_integral_eq {R r : ℝ} (hr : 0 < r) (hR : r < R) (v : ℝ) :
    (∫ u in (0:ℝ)..(2 * π), meanCurv R r u v ^ 2 * areaElt R r u v)
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hs := sqrt_sub_pos hr hR
  rw [intervalIntegral.integral_congr
      (g := fun u => cos u + R ^ 2 / (4 * r) * (1 / (R + r * cos u)))
      (fun u _ => willmore_integrand_eq hr hR u v)]
  have hi1 : IntervalIntegrable (fun u : ℝ => cos u) MeasureTheory.volume 0 (2 * π) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => R ^ 2 / (4 * r) * (1 / (R + r * cos u)))
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul (continuous_inv_radial hr hR)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2]
  rw [integral_cos, intervalIntegral.integral_const_mul, integral_inv_radial hr hR]
  rw [Real.sin_two_pi, Real.sin_zero]
  field_simp
  ring

/-- The Willmore energy `∫∫ H² dA` of the torus of revolution with radii `R > r > 0`. -/
noncomputable def willmoreEnergy (R r : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..(2 * π), ∫ u in (0:ℝ)..(2 * π), meanCurv R r u v ^ 2 * areaElt R r u v

/-- The classical closed formula `W = π² R² / (r √(R² - r²))`. -/
theorem willmoreEnergy_eq {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    willmoreEnergy R r = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hs := sqrt_sub_pos hr hR
  rw [willmoreEnergy, intervalIntegral.integral_congr
      (g := fun _ : ℝ => π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)))
      (fun v _ => inner_integral_eq hr hR v)]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring


/-! ## Minimization: the Clifford torus -/

lemma one_lt_sqrt_two : (1:ℝ) < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

lemma lt_sqrt_two_mul {r : ℝ} (hr : 0 < r) : r < Real.sqrt 2 * r := by
  nlinarith [one_lt_sqrt_two]

/-- The elementary inequality behind the Willmore bound: `2r√(R² - r²) ≤ R²`,
which is equivalent to `(R² - 2r²)² ≥ 0`. -/
lemma two_mul_r_sqrt_le {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * r * Real.sqrt (R ^ 2 - r ^ 2) ≤ R ^ 2 := by
  have hR0 : 0 < R := lt_trans hr hR
  have hsq : (0:ℝ) ≤ R ^ 2 - r ^ 2 := by nlinarith
  have hs2 := Real.sq_sqrt hsq
  have hnn := Real.sqrt_nonneg (R ^ 2 - r ^ 2)
  nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (2 * r * Real.sqrt (R ^ 2 - r ^ 2) - R ^ 2),
    mul_pos hr hR0]

/-- **Willmore's bound for tori of revolution**: the Willmore energy of any torus of
revolution is at least `2π²`. -/
theorem willmoreEnergy_ge {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * π ^ 2 ≤ willmoreEnergy R r := by
  have hs := sqrt_sub_pos hr hR
  have hpi : (0:ℝ) < π ^ 2 := by positivity
  rw [willmoreEnergy_eq hr hR, le_div_iff₀ (by positivity)]
  nlinarith [two_mul_r_sqrt_le hr hR]

/-- The Willmore energy of the Clifford torus (`R = √2 r`) equals `2π²`. -/
theorem willmoreEnergy_clifford {r : ℝ} (hr : 0 < r) :
    willmoreEnergy (Real.sqrt 2 * r) r = 2 * π ^ 2 := by
  have hlt := lt_sqrt_two_mul hr
  have hsq : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [willmoreEnergy_eq hr hlt, hsq]
  rw [show 2 * r ^ 2 - r ^ 2 = r ^ 2 by ring, Real.sqrt_sq hr.le]
  field_simp

/-- Equality in the Willmore bound holds exactly for the Clifford torus `R = √2 r`. -/
theorem willmoreEnergy_eq_iff {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    willmoreEnergy R r = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hR0 : 0 < R := lt_trans hr hR
  have hs := sqrt_sub_pos hr hR
  have hsqnn : (0:ℝ) ≤ R ^ 2 - r ^ 2 := by nlinarith
  have hs2 := Real.sq_sqrt hsqnn
  have hpi : (0:ℝ) < π ^ 2 := by positivity
  constructor
  · intro h
    rw [willmoreEnergy_eq hr hR, div_eq_iff (by positivity)] at h
    have key : R ^ 2 = 2 * (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
      have := mul_left_cancel₀ (ne_of_gt hpi) (a := π ^ 2)
        (b := R ^ 2) (c := 2 * (r * Real.sqrt (R ^ 2 - r ^ 2)))
      apply this
      linarith [h]
    have hzero : (R ^ 2 - 2 * r ^ 2) ^ 2 = 0 := by nlinarith [key, hs2]
    have h2 : R ^ 2 = 2 * r ^ 2 := by nlinarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero]
    have hc : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [Real.sqrt_nonneg 2, mul_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) hr]
  · intro h
    subst h
    exact willmoreEnergy_clifford hr

/-- **The Willmore conjecture for tori of revolution (Willmore's theorem).**

For the family of embedded genus-one surfaces given by the tori of revolution with radii
`R > r > 0`, the Willmore energy `W = ∫∫ H² dA` — computed here from the parametrization
via the first and second fundamental forms — is bounded below by `2π²`, this value is
attained by the Clifford torus `R = √2 r`, and the Clifford torus is the *only* torus of
revolution attaining it.

This is the classical base case of the Willmore conjecture, proved in full generality for
all genus-one immersed surfaces in `S³` (equivalently `ℝ³`) by Marques and Neves. -/
theorem willmore_conjecture :
    (∀ R r : ℝ, 0 < r → r < R → 2 * π ^ 2 ≤ willmoreEnergy R r) ∧
    (∀ r : ℝ, 0 < r → willmoreEnergy (Real.sqrt 2 * r) r = 2 * π ^ 2) ∧
    (∀ R r : ℝ, 0 < r → r < R → (willmoreEnergy R r = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r)) :=
  ⟨fun _ _ hr hR => willmoreEnergy_ge hr hR, fun _ hr => willmoreEnergy_clifford hr,
    fun _ _ hr hR => willmoreEnergy_eq_iff hr hR⟩

end Frontier

