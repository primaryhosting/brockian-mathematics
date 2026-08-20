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

open scoped Real

namespace Frontier

/-! ## Euclidean 3-space as `ℝ × ℝ × ℝ`

We use the plain product type and equip it with an explicit dot product and cross
product, so that all differential-geometric quantities below are literally the
classical ones. -/

/-- Ambient space `ℝ³`. -/
abbrev E3 := ℝ × ℝ × ℝ

/-- The Euclidean dot product on `ℝ³`. -/
def dot3 (a b : E3) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- The cross product on `ℝ³`. -/
def cross3 (a b : E3) : E3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)

/-- The Euclidean norm on `ℝ³`. -/
noncomputable def nrm3 (a : E3) : ℝ := Real.sqrt (dot3 a a)

/-- Componentwise derivative of an `ℝ³`-valued function of one real variable. -/
theorem hasDerivAt_triple {f g h : ℝ → ℝ} {f' g' h' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) (hh : HasDerivAt h h' x) :
    HasDerivAt (fun t => ((f t, g t, h t) : E3)) (f', g', h') x :=
  hf.prodMk (hg.prodMk hh)

/-! ## The torus of revolution -/

/-- The standard immersion of the torus of revolution with centre-circle radius `R`
and tube radius `r`: `(u, v) ↦ ((R + r cos u) cos v, (R + r cos u) sin v, r sin u)`. -/
noncomputable def torusImm (R r u v : ℝ) : E3 :=
  ((R + r * Real.cos u) * Real.cos v, (R + r * Real.cos u) * Real.sin v, r * Real.sin u)

/-- First partial derivative of `torusImm` in the `u` direction. -/
noncomputable def dU (R r u v : ℝ) : E3 := deriv (fun t => torusImm R r t v) u

/-- First partial derivative of `torusImm` in the `v` direction. -/
noncomputable def dV (R r u v : ℝ) : E3 := deriv (fun t => torusImm R r u t) v

/-- Second partial derivative `∂²/∂u²` of `torusImm`. -/
noncomputable def dUU (R r u v : ℝ) : E3 := deriv (fun t => dU R r t v) u

/-- Mixed second partial derivative `∂²/∂v∂u` of `torusImm`. -/
noncomputable def dUV (R r u v : ℝ) : E3 := deriv (fun t => dU R r u t) v

/-- Second partial derivative `∂²/∂v²` of `torusImm`. -/
noncomputable def dVV (R r u v : ℝ) : E3 := deriv (fun t => dV R r u t) v

/-- The (unnormalised) normal field `X_u × X_v`. -/
noncomputable def normalVec (R r u v : ℝ) : E3 := cross3 (dU R r u v) (dV R r u v)

/-- The unit normal field `(X_u × X_v) / |X_u × X_v|`. -/
noncomputable def unitNormal (R r u v : ℝ) : E3 :=
  ((nrm3 (normalVec R r u v))⁻¹ * (normalVec R r u v).1,
   (nrm3 (normalVec R r u v))⁻¹ * (normalVec R r u v).2.1,
   (nrm3 (normalVec R r u v))⁻¹ * (normalVec R r u v).2.2)

/-- Coefficient `E` of the first fundamental form. -/
noncomputable def firstE (R r u v : ℝ) : ℝ := dot3 (dU R r u v) (dU R r u v)
/-- Coefficient `F` of the first fundamental form. -/
noncomputable def firstF (R r u v : ℝ) : ℝ := dot3 (dU R r u v) (dV R r u v)
/-- Coefficient `G` of the first fundamental form. -/
noncomputable def firstG (R r u v : ℝ) : ℝ := dot3 (dV R r u v) (dV R r u v)

/-- Coefficient `e` of the second fundamental form. -/
noncomputable def secondE (R r u v : ℝ) : ℝ := dot3 (dUU R r u v) (unitNormal R r u v)
/-- Coefficient `f` of the second fundamental form. -/
noncomputable def secondF (R r u v : ℝ) : ℝ := dot3 (dUV R r u v) (unitNormal R r u v)
/-- Coefficient `g` of the second fundamental form. -/
noncomputable def secondG (R r u v : ℝ) : ℝ := dot3 (dVV R r u v) (unitNormal R r u v)

/-- The mean curvature, in terms of the fundamental forms:
`H = (eG - 2fF + gE) / (2 (EG - F²))`. -/
noncomputable def meanCurv (R r u v : ℝ) : ℝ :=
  (secondE R r u v * firstG R r u v - 2 * secondF R r u v * firstF R r u v
      + secondG R r u v * firstE R r u v)
    / (2 * (firstE R r u v * firstG R r u v - firstF R r u v ^ 2))

/-- The area element `√(EG - F²)`. -/
noncomputable def areaElt (R r u v : ℝ) : ℝ :=
  Real.sqrt (firstE R r u v * firstG R r u v - firstF R r u v ^ 2)

/-- The Willmore energy `∫ H² dA` of the torus of revolution with radii `R > r > 0`. -/
noncomputable def willmoreEnergyRotational (R r : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..(2 * π), ∫ u in (0 : ℝ)..(2 * π), meanCurv R r u v ^ 2 * areaElt R r u v

/-! ### The partial derivatives of the immersion -/

theorem hasDerivAt_torusImm_u (R r v u : ℝ) :
    HasDerivAt (fun t => torusImm R r t v)
      (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u) u := by
  have h1 : HasDerivAt (fun t => R + r * Real.cos t) (-(r * Real.sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add R
  exact hasDerivAt_triple (h1.mul_const _) (h1.mul_const _)
    (by simpa using (Real.hasDerivAt_sin u).const_mul r)

theorem hasDerivAt_torusImm_v (R r u v : ℝ) :
    HasDerivAt (fun t => torusImm R r u t)
      (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0) v :=
  hasDerivAt_triple (by simpa using (Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u))
    (by simpa using (Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u)) (hasDerivAt_const _ _)

theorem dU_eq (R r u v : ℝ) :
    dU R r u v = (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u) :=
  (hasDerivAt_torusImm_u R r v u).deriv

theorem dV_eq (R r u v : ℝ) :
    dV R r u v =
      (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0) :=
  (hasDerivAt_torusImm_v R r u v).deriv

theorem dUU_eq (R r u v : ℝ) :
    dUU R r u v =
      (-(r * Real.cos u) * Real.cos v, -(r * Real.cos u) * Real.sin v, -(r * Real.sin u)) := by
  have hfun : (fun t => dU R r t v) =
      fun t => ((-(r * Real.sin t) * Real.cos v, -(r * Real.sin t) * Real.sin v,
        r * Real.cos t) : E3) := funext fun t => dU_eq R r t v
  have h1 : HasDerivAt (fun t => -(r * Real.sin t)) (-(r * Real.cos u)) u := by
    simpa using ((Real.hasDerivAt_sin u).const_mul r).neg
  rw [dUU, hfun]
  exact (hasDerivAt_triple (h1.mul_const _) (h1.mul_const _)
    (by simpa using (Real.hasDerivAt_cos u).const_mul r)).deriv

theorem dUV_eq (R r u v : ℝ) :
    dUV R r u v = (r * Real.sin u * Real.sin v, -(r * Real.sin u) * Real.cos v, 0) := by
  have hfun : (fun t => dU R r u t) =
      fun t => ((-(r * Real.sin u) * Real.cos t, -(r * Real.sin u) * Real.sin t,
        r * Real.cos u) : E3) := funext fun t => dU_eq R r u t
  rw [dUV, hfun]
  refine HasDerivAt.deriv (hasDerivAt_triple ?_ ?_ (hasDerivAt_const _ _))
  · simpa [mul_comm] using (Real.hasDerivAt_cos v).const_mul (-(r * Real.sin u))
  · simpa using (Real.hasDerivAt_sin v).const_mul (-(r * Real.sin u))

theorem dVV_eq (R r u v : ℝ) :
    dVV R r u v =
      (-((R + r * Real.cos u) * Real.cos v), -((R + r * Real.cos u) * Real.sin v), 0) := by
  have hfun : (fun t => dV R r u t) =
      fun t => ((-((R + r * Real.cos u) * Real.sin t), (R + r * Real.cos u) * Real.cos t,
        0) : E3) := funext fun t => dV_eq R r u t
  rw [dVV, hfun]
  refine HasDerivAt.deriv (hasDerivAt_triple ?_ ?_ (hasDerivAt_const _ _))
  · simpa using ((Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u)).neg
  · simpa using (Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u)

/-! ### The fundamental forms of the torus of revolution -/

theorem firstE_eq (R r u v : ℝ) : firstE R r u v = r ^ 2 := by
  have hu := Real.sin_sq_add_cos_sq u
  have hv := Real.sin_sq_add_cos_sq v
  simp only [firstE, dot3, dU_eq]
  linear_combination (r ^ 2 * Real.sin u ^ 2) * hv + r ^ 2 * hu

theorem firstF_eq (R r u v : ℝ) : firstF R r u v = 0 := by
  simp only [firstF, dot3, dU_eq, dV_eq]
  ring

theorem firstG_eq (R r u v : ℝ) : firstG R r u v = (R + r * Real.cos u) ^ 2 := by
  have hv := Real.sin_sq_add_cos_sq v
  simp only [firstG, dot3, dV_eq]
  linear_combination ((R + r * Real.cos u) ^ 2) * hv

theorem normalVec_eq (R r u v : ℝ) :
    normalVec R r u v =
      (-(r * (R + r * Real.cos u) * Real.cos u * Real.cos v),
       -(r * (R + r * Real.cos u) * Real.cos u * Real.sin v),
       -(r * (R + r * Real.cos u) * Real.sin u)) := by
  have hv := Real.sin_sq_add_cos_sq v
  simp only [normalVec, cross3, dU_eq, dV_eq, Prod.mk.injEq]
  exact ⟨by ring, by ring, by linear_combination (-(r * (R + r * Real.cos u) * Real.sin u)) * hv⟩

theorem nrm3_normalVec (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    nrm3 (normalVec R r u v) = r * (R + r * Real.cos u) := by
  have hu := Real.sin_sq_add_cos_sq u
  have hv := Real.sin_sq_add_cos_sq v
  have : dot3 (normalVec R r u v) (normalVec R r u v) = (r * (R + r * Real.cos u)) ^ 2 := by
    simp only [dot3, normalVec_eq]
    linear_combination (r ^ 2 * (R + r * Real.cos u) ^ 2 * Real.cos u ^ 2) * hv
      + (r ^ 2 * (R + r * Real.cos u) ^ 2) * hu
  rw [nrm3, this, Real.sqrt_sq (by positivity)]

theorem unitNormal_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    unitNormal R r u v =
      (-(Real.cos u * Real.cos v), -(Real.cos u * Real.sin v), -Real.sin u) := by
  have hne : r * (R + r * Real.cos u) ≠ 0 := by positivity
  rw [unitNormal, nrm3_normalVec R r u v hr hD, normalVec_eq]
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

theorem secondE_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    secondE R r u v = r := by
  have hu := Real.sin_sq_add_cos_sq u
  have hv := Real.sin_sq_add_cos_sq v
  simp only [secondE, dot3, dUU_eq, unitNormal_eq R r u v hr hD]
  linear_combination (r * Real.cos u ^ 2) * hv + r * hu

theorem secondF_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    secondF R r u v = 0 := by
  simp only [secondF, dot3, dUV_eq, unitNormal_eq R r u v hr hD]
  ring

theorem secondG_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    secondG R r u v = (R + r * Real.cos u) * Real.cos u := by
  have hv := Real.sin_sq_add_cos_sq v
  simp only [secondG, dot3, dVV_eq, unitNormal_eq R r u v hr hD]
  linear_combination ((R + r * Real.cos u) * Real.cos u) * hv

/-- The mean curvature of the torus of revolution: `H = (R + 2r cos u) / (2 r (R + r cos u))`. -/
theorem meanCurv_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    meanCurv R r u v = (R + 2 * r * Real.cos u) / (2 * r * (R + r * Real.cos u)) := by
  have hne : r ≠ 0 := ne_of_gt hr
  have hDne : R + r * Real.cos u ≠ 0 := ne_of_gt hD
  simp only [meanCurv, firstE_eq, firstF_eq, firstG_eq, secondE_eq R r u v hr hD,
    secondF_eq R r u v hr hD, secondG_eq R r u v hr hD]
  field_simp
  ring

/-- The area element of the torus of revolution: `dA = r (R + r cos u) du dv`. -/
theorem areaElt_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    areaElt R r u v = r * (R + r * Real.cos u) := by
  have : firstE R r u v * firstG R r u v - firstF R r u v ^ 2
      = (r * (R + r * Real.cos u)) ^ 2 := by
    rw [firstE_eq, firstF_eq, firstG_eq]; ring
  rw [areaElt, this, Real.sqrt_sq (by positivity)]

/-- The pointwise Willmore integrand `H² dA` of the torus of revolution. -/
theorem integrand_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    meanCurv R r u v ^ 2 * areaElt R r u v
      = (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)) := by
  have hne : r ≠ 0 := ne_of_gt hr
  have hDne : R + r * Real.cos u ≠ 0 := ne_of_gt hD
  rw [meanCurv_eq R r u v hr hD, areaElt_eq R r u v hr hD]
  field_simp
  ring


/-! ## The Willmore energy of the torus of revolution

We integrate `H² dA` explicitly.  The antiderivative

`Φ(u) = sin u + R² (u - 2 arctan (r sin u / (R + S + r cos u))) / (4 r S)`,  `S = √(R² - r²)`,

is smooth on all of `ℝ` (its denominator `R + S + r cos u` never vanishes), which lets us
apply the fundamental theorem of calculus on `[0, 2π]` without any splitting. -/

/-- A global antiderivative of the Willmore integrand `(R + 2r cos u)² / (4r(R + r cos u))`. -/
noncomputable def willmorePrimitive (R r u : ℝ) : ℝ :=
  Real.sin u + R ^ 2 * (u - 2 * Real.arctan (r * Real.sin u /
    (R + Real.sqrt (R ^ 2 - r ^ 2) + r * Real.cos u))) / (4 * r * Real.sqrt (R ^ 2 - r ^ 2))

theorem hasDerivAt_willmorePrimitive (R r : ℝ) (hr : 0 < r) (hR : r < R) (u : ℝ) :
    HasDerivAt (willmorePrimitive R r)
      ((R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u))) u := by
  set S := Real.sqrt (R ^ 2 - r ^ 2) with hSdef
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hS0 : 0 < S := Real.sqrt_pos.2 (by nlinarith)
  have hSsq : S ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hcos : -1 ≤ Real.cos u := Real.neg_one_le_cos u
  have hcos' : Real.cos u ≤ 1 := Real.cos_le_one u
  have hD : 0 < R + r * Real.cos u := by nlinarith
  have hM : 0 < R + S + r * Real.cos u := by nlinarith
  have hRS : (0:ℝ) < R + S := by nlinarith
  have hnum : HasDerivAt (fun t => r * Real.sin t) (r * Real.cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul r
  have hden : HasDerivAt (fun t => R + S + r * Real.cos t) (-(r * Real.sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add (R + S)
  have hq : HasDerivAt (fun t => r * Real.sin t / (R + S + r * Real.cos t))
      ((r * Real.cos u * (R + S + r * Real.cos u) - r * Real.sin u * -(r * Real.sin u))
        / (R + S + r * Real.cos u) ^ 2) u := hnum.div hden (ne_of_gt hM)
  have hat := hq.arctan
  have h := (Real.hasDerivAt_sin u).add
    ((((hasDerivAt_id u).sub (hat.const_mul 2)).const_mul (R ^ 2)).div_const (4 * r * S))
  refine h.congr_deriv ?_
  have hpyth : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  have hMne : (R + S + r * Real.cos u) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hM)
  have hDne : R + r * Real.cos u ≠ 0 := ne_of_gt hD
  have h1 : 1 + (r * Real.sin u / (R + S + r * Real.cos u)) ^ 2
      = 2 * (R + S) * (R + r * Real.cos u) / (R + S + r * Real.cos u) ^ 2 := by
    field_simp
    linear_combination r ^ 2 * hpyth + hSsq
  have h2 : r * Real.cos u * (R + S + r * Real.cos u) - r * Real.sin u * -(r * Real.sin u)
      = r * Real.cos u * (R + S) + r ^ 2 := by
    linear_combination r ^ 2 * hpyth
  have key : 1 - 2 * (1 / (1 + (r * Real.sin u / (R + S + r * Real.cos u)) ^ 2) *
      ((r * Real.cos u * (R + S + r * Real.cos u) - r * Real.sin u * -(r * Real.sin u))
        / (R + S + r * Real.cos u) ^ 2)) = S / (R + r * Real.cos u) := by
    rw [h1, h2, div_mul_div_comm, one_mul, div_mul_cancel₀ _ hMne]
    field_simp
    linear_combination -hSsq
  rw [key]
  have hne : (4:ℝ) * r * (R + r * Real.cos u) ≠ 0 := by positivity
  have hstep : R ^ 2 * (S / (R + r * Real.cos u)) / (4 * r * S)
      = R ^ 2 / (4 * r * (R + r * Real.cos u)) := by
    rw [div_eq_div_iff (by positivity) hne, mul_comm (R ^ 2) (S / (R + r * Real.cos u)),
      mul_assoc, div_mul_eq_mul_div, div_eq_iff hDne]
    ring
  rw [hstep, eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
  ring

/-- The Willmore integrand of the torus of revolution is continuous. -/
theorem continuous_willmoreIntegrand (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    Continuous fun u : ℝ => (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
  have hcos : -1 ≤ Real.cos u := Real.neg_one_le_cos u
  have hD : 0 < R + r * Real.cos u := by nlinarith [Real.cos_le_one u]
  positivity

/-- The `u`-integral of the Willmore integrand over one full period. -/
theorem integral_willmoreIntegrand (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    (∫ u in (0:ℝ)..(2 * π), (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hS0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_willmorePrimitive R r hr hR x)
    ((continuous_willmoreIntegrand R r hr hR).intervalIntegrable _ _)]
  simp only [willmorePrimitive, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  rw [show r * (0:ℝ) / (R + Real.sqrt (R ^ 2 - r ^ 2) + r * 1) = 0 by ring]
  simp only [Real.arctan_zero, mul_zero, sub_zero, zero_add]
  have hrne : r ≠ 0 := ne_of_gt hr
  have hSne : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hS0
  field_simp
  ring

/-- **The Willmore energy of the torus of revolution.**
For radii `0 < r < R`, `∫ H² dA = π² R² / (r √(R² - r²))`. -/
theorem willmoreEnergyRotational_eq (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    willmoreEnergyRotational R r = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hS0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hinner : ∀ v : ℝ,
      (∫ u in (0:ℝ)..(2 * π), meanCurv R r u v ^ 2 * areaElt R r u v)
        = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    intro v
    rw [intervalIntegral.integral_congr
      (g := fun u => (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      (fun u _ => integrand_eq R r u v hr (by nlinarith [Real.neg_one_le_cos u]))]
    exact integral_willmoreIntegrand R r hr hR
  rw [willmoreEnergyRotational]
  simp only [hinner]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hrne : r ≠ 0 := ne_of_gt hr
  have hSne : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hS0
  field_simp

/-! ## The sharp lower bound: the Clifford ratio `R = √2 r` -/

/-- The sharp lower bound `π² R² / (r √(R² - r²)) ≥ 2π²` for `0 < r < R`. -/
theorem two_pi_sq_le_energy (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    2 * π ^ 2 ≤ π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  set S := Real.sqrt (R ^ 2 - r ^ 2) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 (by nlinarith)
  have hSsq : S ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hkey : 2 * (r * S) ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (r * S), sq_nonneg (R ^ 2 - 2 * r * S),
      mul_pos hr hS0]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos, sq_nonneg π, mul_pos hr hS0]

/-- Equality in the Willmore bound holds exactly for the Clifford ratio `R = √2 r`. -/
theorem energy_eq_two_pi_sq_iff (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hpi : (0:ℝ) < π := Real.pi_pos
  set S := Real.sqrt (R ^ 2 - r ^ 2) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 (by nlinarith)
  have hSsq : S ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi2 : (0:ℝ) < π ^ 2 := by positivity
  rw [div_eq_iff (by positivity)]
  constructor
  · intro h
    have hR2 : R ^ 2 = 2 * (r * S) :=
      mul_left_cancel₀ (ne_of_gt hpi2) (by linear_combination h)
    have hsq : R ^ 2 = 2 * r ^ 2 := by
      nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), mul_pos hr hS0]
    nlinarith [sq_nonneg (R - Real.sqrt 2 * r), mul_pos h2pos hr]
  · intro h
    subst h
    have hSval : S = r := by
      rw [hSdef, show (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 by linear_combination r ^ 2 * h2]
      exact Real.sqrt_sq hr.le
    rw [hSval]
    linear_combination (π ^ 2 * r ^ 2) * h2

/-! ## Main statement -/

/--
**Willmore's theorem for tori of revolution** (the rotationally symmetric case of the
Willmore conjecture, proved in full generality by Marques and Neves).

For the torus of revolution in `ℝ³` with centre-circle radius `R` and tube radius `r`,
`0 < r < R`, whose mean curvature `H` and area element `dA` are computed here from the
first and second fundamental forms of the explicit immersion
`(u, v) ↦ ((R + r cos u) cos v, (R + r cos u) sin v, r sin u)`, the Willmore energy satisfies

`∫ H² dA ≥ 2π²`,

with equality if and only if `R = √2 · r`, i.e. exactly for the torus which is the
stereographic image of the Clifford torus in `S³`.
-/
theorem willmore_conjecture {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * π ^ 2 ≤ willmoreEnergyRotational R r ∧
      (willmoreEnergyRotational R r = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r) := by
  rw [willmoreEnergyRotational_eq R r hr hR]
  exact ⟨two_pi_sq_le_energy R r hr hR, energy_eq_two_pi_sq_iff R r hr hR⟩

/-- `1 < √2`. -/
theorem one_lt_sqrt_two : (1:ℝ) < Real.sqrt 2 := by
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The Clifford ratio realises the minimum**: the torus of revolution with `R = √2 r`
(the stereographic image of the Clifford torus) has Willmore energy exactly `2π²`. -/
theorem willmoreEnergyRotational_clifford (r : ℝ) (hr : 0 < r) :
    willmoreEnergyRotational (Real.sqrt 2 * r) r = 2 * π ^ 2 := by
  have hR : r < Real.sqrt 2 * r := by nlinarith [one_lt_sqrt_two]
  exact ((willmore_conjecture hr hR).2).2 rfl

/-- **The Clifford torus minimizes the Willmore energy among tori of revolution**:
`2π²` is the least element of the set of Willmore energies of tori of revolution. -/
theorem willmore_isLeast :
    IsLeast {W : ℝ | ∃ R r : ℝ, 0 < r ∧ r < R ∧ W = willmoreEnergyRotational R r} (2 * π ^ 2) := by
  constructor
  · exact ⟨Real.sqrt 2, 1, one_pos, by nlinarith [one_lt_sqrt_two],
      by simpa using (willmoreEnergyRotational_clifford 1 one_pos).symm⟩
  · rintro W ⟨R, r, hr, hR, rfl⟩
    exact (willmore_conjecture hr hR).1

end Frontier

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

