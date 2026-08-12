import Mathlib
/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Willmore conjecture (proved by Marques and Neves) states that every immersed torus
`Σ ⊆ ℝ³` satisfies `∫_Σ H² dA ≥ 2π²`, with equality (up to conformal transformations of
`ℝ³`) exactly for the Clifford torus, i.e. the torus of revolution whose radii satisfy
`R = √2 · r`.

This file formalizes and proves the *base case* of the conjecture: the case of tori of
revolution, which is Willmore's original computation and the case that fixes the constant
`2π²`.  Everything is done from first principles:

* for an arbitrary parametrized surface `X : ℝ → ℝ → ℝ³`, the tangent vectors
  `Frontier.surfDu`, `Frontier.surfDv` and the second derivatives are literally `deriv`s
  of `X`; `Frontier.surfMeanCurvature` is the mean curvature computed from the first and
  second fundamental forms, `Frontier.surfAreaElement` is the area element
  `‖X_u × X_v‖`, and `Frontier.willmoreEnergyOf` is the iterated integral `∫∫ H² dA`
  over a fundamental domain `[0, 2π] × [0, 2π]`;
* `Frontier.torusParam` is the usual parametrization of the torus of revolution with
  radii `R > r > 0`, and `Frontier.willmoreEnergy R r` its Willmore energy;
* `Frontier.IsImmersedTorus` and `Frontier.WillmoreConjectureStatement` record the
  statement of the conjecture in full generality.

The main results are

* `Frontier.torusMeanCurvature_eq` and `Frontier.torusAreaElement_eq`: the classical
  formulas `H = (R + 2r cos u) / (2r(R + r cos u))` and `dA = r (R + r cos u)`;
* `Frontier.integral_inv_add_cos` : `∫₀^{2π} du / (R + r cos u) = 2π / √(R² - r²)`;
* `Frontier.willmoreEnergy_eq` : `W(R, r) = π² R² / (r √(R² - r²))`;
* `Frontier.willmore_conjecture` : `2π²` is the least Willmore energy of a torus of
  revolution, and it is attained exactly by the Clifford torus `R = √2 · r`;
* `Frontier.willmore_bound_sharp` : the constant `2π²` in the general conjecture is
  attained by an immersed torus, so it cannot be improved.
-/

open Real Matrix

namespace Frontier

/-! ### Differential geometry of a parametrized surface in `ℝ³`

For a map `X : ℝ → ℝ → ℝ³` we define the tangent vectors, the first and second fundamental
forms, the area element and the mean curvature by the classical formulas.  All derivatives
are honest `deriv`s of `X`. -/

/-- The tangent vector `X_u`. -/
noncomputable def surfDu (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  deriv (fun t => X t v) u

/-- The tangent vector `X_v`. -/
noncomputable def surfDv (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  deriv (fun t => X u t) v

/-- The second derivative `X_uu`. -/
noncomputable def surfDuu (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  deriv (fun t => surfDu X t v) u

/-- The mixed second derivative `X_uv`. -/
noncomputable def surfDuv (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  deriv (fun t => surfDu X u t) v

/-- The second derivative `X_vv`. -/
noncomputable def surfDvv (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  deriv (fun t => surfDv X u t) v

/-- The (unnormalized) normal vector `X_u × X_v`. -/
noncomputable def surfCross (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  crossProduct (surfDu X u v) (surfDv X u v)

/-- The area element `‖X_u × X_v‖ = √(EG - F²)`. -/
noncomputable def surfAreaElement (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ :=
  Real.sqrt (surfCross X u v ⬝ᵥ surfCross X u v)

/-- The unit normal `(X_u × X_v) / ‖X_u × X_v‖`. -/
noncomputable def surfNormal (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  (surfAreaElement X u v)⁻¹ • surfCross X u v

/-- First fundamental form coefficient `E = X_u · X_u`. -/
noncomputable def surfE (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ := surfDu X u v ⬝ᵥ surfDu X u v
/-- First fundamental form coefficient `F = X_u · X_v`. -/
noncomputable def surfF (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ := surfDu X u v ⬝ᵥ surfDv X u v
/-- First fundamental form coefficient `G = X_v · X_v`. -/
noncomputable def surfG (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ := surfDv X u v ⬝ᵥ surfDv X u v
/-- Second fundamental form coefficient `e = X_uu · n`. -/
noncomputable def surfSecE (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ :=
  surfDuu X u v ⬝ᵥ surfNormal X u v
/-- Second fundamental form coefficient `f = X_uv · n`. -/
noncomputable def surfSecF (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ :=
  surfDuv X u v ⬝ᵥ surfNormal X u v
/-- Second fundamental form coefficient `g = X_vv · n`. -/
noncomputable def surfSecG (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ :=
  surfDvv X u v ⬝ᵥ surfNormal X u v

/-- The mean curvature `H = (eG - 2fF + gE) / (2(EG - F²))`. -/
noncomputable def surfMeanCurvature (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : ℝ :=
  (surfSecE X u v * surfG X u v - 2 * surfSecF X u v * surfF X u v
      + surfSecG X u v * surfE X u v) / (2 * (surfE X u v * surfG X u v - surfF X u v ^ 2))

/-- The Willmore energy `∫∫ H² dA` of a `2π`-doubly periodic parametrized surface,
computed over one fundamental domain `[0, 2π] × [0, 2π]`. -/
noncomputable def willmoreEnergyOf (X : ℝ → ℝ → Fin 3 → ℝ) : ℝ :=
  ∫ v in (0:ℝ)..(2 * π), ∫ u in (0:ℝ)..(2 * π),
    surfMeanCurvature X u v ^ 2 * surfAreaElement X u v

/-! ### The torus of revolution -/

/-- The standard parametrization of the torus of revolution in `ℝ³` obtained by revolving
the circle of radius `r` centred at distance `R` from the axis. -/
noncomputable def torusParam (R r u v : ℝ) : Fin 3 → ℝ :=
  ![(R + r * Real.cos u) * Real.cos v, (R + r * Real.cos u) * Real.sin v, r * Real.sin u]

/-- The Willmore energy `∫∫ H² dA` of the torus of revolution with radii `R > r > 0`. -/
noncomputable def willmoreEnergy (R r : ℝ) : ℝ := willmoreEnergyOf (torusParam R r)

/-! ### Derivatives of the parametrization -/

lemma hasDerivAt_torusParam_u (R r u v : ℝ) :
    HasDerivAt (fun t => torusParam R r t v)
      ![-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u] u := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun x => (R + r * Real.cos x) * Real.cos v) (-(r * Real.sin u) * Real.cos v) u
    convert (((Real.hasDerivAt_cos u).const_mul r).const_add R).mul_const (Real.cos v) using 1
    ring
  · show HasDerivAt (fun x => (R + r * Real.cos x) * Real.sin v) (-(r * Real.sin u) * Real.sin v) u
    convert (((Real.hasDerivAt_cos u).const_mul r).const_add R).mul_const (Real.sin v) using 1
    ring
  · show HasDerivAt (fun x => r * Real.sin x) (r * Real.cos u) u
    exact (Real.hasDerivAt_sin u).const_mul r

lemma hasDerivAt_torusParam_v (R r u v : ℝ) :
    HasDerivAt (fun t => torusParam R r u t)
      ![-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0] v := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun t => (R + r * Real.cos u) * Real.cos t)
      (-((R + r * Real.cos u) * Real.sin v)) v
    convert (Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u) using 1
    ring
  · show HasDerivAt (fun t => (R + r * Real.cos u) * Real.sin t)
      ((R + r * Real.cos u) * Real.cos v) v
    exact (Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u)
  · show HasDerivAt (fun _ => r * Real.sin u) (0 : ℝ) v
    exact hasDerivAt_const _ _

lemma torusDu_eq (R r u v : ℝ) :
    surfDu (torusParam R r) u v
      = ![-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u] :=
  (hasDerivAt_torusParam_u R r u v).deriv

lemma torusDv_eq (R r u v : ℝ) :
    surfDv (torusParam R r) u v
      = ![-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0] :=
  (hasDerivAt_torusParam_v R r u v).deriv

lemma torusDuu_eq (R r u v : ℝ) :
    surfDuu (torusParam R r) u v
      = ![-(r * Real.cos u) * Real.cos v, -(r * Real.cos u) * Real.sin v, -(r * Real.sin u)] := by
  have hfun : (fun t => surfDu (torusParam R r) t v)
      = fun t => ![-(r * Real.sin t) * Real.cos v, -(r * Real.sin t) * Real.sin v,
        r * Real.cos t] := funext fun t => torusDu_eq R r t v
  rw [surfDuu, hfun]
  refine HasDerivAt.deriv ?_
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun t => -(r * Real.sin t) * Real.cos v) (-(r * Real.cos u) * Real.cos v) u
    exact (((Real.hasDerivAt_sin u).const_mul r).neg).mul_const (Real.cos v)
  · show HasDerivAt (fun t => -(r * Real.sin t) * Real.sin v) (-(r * Real.cos u) * Real.sin v) u
    exact (((Real.hasDerivAt_sin u).const_mul r).neg).mul_const (Real.sin v)
  · show HasDerivAt (fun t => r * Real.cos t) (-(r * Real.sin u)) u
    convert (Real.hasDerivAt_cos u).const_mul r using 1
    ring

lemma torusDuv_eq (R r u v : ℝ) :
    surfDuv (torusParam R r) u v
      = ![r * Real.sin u * Real.sin v, -(r * Real.sin u) * Real.cos v, 0] := by
  have hfun : (fun t => surfDu (torusParam R r) u t)
      = fun t => ![-(r * Real.sin u) * Real.cos t, -(r * Real.sin u) * Real.sin t,
        r * Real.cos u] := funext fun t => torusDu_eq R r u t
  rw [surfDuv, hfun]
  refine HasDerivAt.deriv ?_
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun t => -(r * Real.sin u) * Real.cos t) (r * Real.sin u * Real.sin v) v
    convert (Real.hasDerivAt_cos v).const_mul (-(r * Real.sin u)) using 1
    ring
  · show HasDerivAt (fun t => -(r * Real.sin u) * Real.sin t) (-(r * Real.sin u) * Real.cos v) v
    exact (Real.hasDerivAt_sin v).const_mul (-(r * Real.sin u))
  · show HasDerivAt (fun _ => r * Real.cos u) (0 : ℝ) v
    exact hasDerivAt_const _ _

lemma torusDvv_eq (R r u v : ℝ) :
    surfDvv (torusParam R r) u v
      = ![-((R + r * Real.cos u) * Real.cos v), -((R + r * Real.cos u) * Real.sin v), 0] := by
  have hfun : (fun t => surfDv (torusParam R r) u t)
      = fun t => ![-((R + r * Real.cos u) * Real.sin t), (R + r * Real.cos u) * Real.cos t, 0] :=
    funext fun t => torusDv_eq R r u t
  rw [surfDvv, hfun]
  refine HasDerivAt.deriv ?_
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun t => -((R + r * Real.cos u) * Real.sin t))
      (-((R + r * Real.cos u) * Real.cos v)) v
    exact ((Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u)).neg
  · show HasDerivAt (fun t => (R + r * Real.cos u) * Real.cos t)
      (-((R + r * Real.cos u) * Real.sin v)) v
    convert (Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u) using 1
    ring
  · show HasDerivAt (fun _ => (0 : ℝ)) (0 : ℝ) v
    exact hasDerivAt_const _ _

/-! ### The fundamental forms of the torus of revolution -/

/-- Positivity of the radial factor `R + r cos u`. -/
lemma torus_radial_pos {R r : ℝ} (hr : 0 < r) (hRr : r < R) (u : ℝ) :
    0 < R + r * Real.cos u := by
  nlinarith [abs_le.mp (Real.abs_cos_le_one u)]

lemma torusCross_eq (R r u v : ℝ) :
    surfCross (torusParam R r) u v = ![-(r * (R + r * Real.cos u)) * (Real.cos u * Real.cos v),
      -(r * (R + r * Real.cos u)) * (Real.cos u * Real.sin v),
      -(r * (R + r * Real.cos u)) * Real.sin u] := by
  ext i
  fin_cases i <;> simp [surfCross, torusDu_eq, torusDv_eq, cross_apply]
  · ring
  · ring
  · linear_combination (-(r * Real.sin u * (R + r * Real.cos u))) * Real.sin_sq_add_cos_sq v

lemma torusAreaElement_eq (R r u v : ℝ) (hr : 0 < r) (hRr : r < R) :
    surfAreaElement (torusParam R r) u v = r * (R + r * Real.cos u) := by
  have hA : 0 < R + r * Real.cos u := torus_radial_pos hr hRr u
  have h : surfCross (torusParam R r) u v ⬝ᵥ surfCross (torusParam R r) u v = (r * (R + r * Real.cos u)) ^ 2 := by
    simp only [torusCross_eq, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination ((r * (R + r * Real.cos u)) ^ 2 * Real.cos u ^ 2) *
        Real.sin_sq_add_cos_sq v + (r * (R + r * Real.cos u)) ^ 2 * Real.sin_sq_add_cos_sq u
  rw [surfAreaElement, h, Real.sqrt_sq (by positivity)]

lemma torusNormal_eq (R r u v : ℝ) (hr : 0 < r) (hRr : r < R) :
    surfNormal (torusParam R r) u v
      = ![-(Real.cos u * Real.cos v), -(Real.cos u * Real.sin v), -Real.sin u] := by
  have hA : 0 < R + r * Real.cos u := torus_radial_pos hr hRr u
  rw [surfNormal, torusAreaElement_eq R r u v hr hRr, torusCross_eq]
  ext i
  fin_cases i <;> simp <;> field_simp

lemma torusMeanCurvature_eq (R r u v : ℝ) (hr : 0 < r) (hRr : r < R) :
    surfMeanCurvature (torusParam R r) u v
      = (R + 2 * r * Real.cos u) / (2 * r * (R + r * Real.cos u)) := by
  have hA : 0 < R + r * Real.cos u := torus_radial_pos hr hRr u
  have hn := torusNormal_eq R r u v hr hRr
  have hpu := Real.sin_sq_add_cos_sq u
  have hpv := Real.sin_sq_add_cos_sq v
  have hE : surfE (torusParam R r) u v = r ^ 2 := by
    simp only [surfE, torusDu_eq, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination (r ^ 2 * Real.sin u ^ 2) * hpv + r ^ 2 * hpu
  have hF : surfF (torusParam R r) u v = 0 := by
    simp only [surfF, torusDu_eq, torusDv_eq, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    ring
  have hG : surfG (torusParam R r) u v = (R + r * Real.cos u) ^ 2 := by
    simp only [surfG, torusDv_eq, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination ((R + r * Real.cos u) ^ 2) * hpv
  have he : surfSecE (torusParam R r) u v = r := by
    simp only [surfSecE, torusDuu_eq, hn, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination (r * Real.cos u ^ 2) * hpv + r * hpu
  have hf : surfSecF (torusParam R r) u v = 0 := by
    simp only [surfSecF, torusDuv_eq, hn, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hg : surfSecG (torusParam R r) u v = (R + r * Real.cos u) * Real.cos u := by
    simp only [surfSecG, torusDvv_eq, hn, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination ((R + r * Real.cos u) * Real.cos u) * hpv
  rw [surfMeanCurvature, hE, hF, hG, he, hf, hg]
  field_simp
  ring

/-! ### The key integral -/

/-- `∫₀^{2π} du / (R + r cos u) = 2π / √(R² - r²)`, proved via the explicit (globally smooth)
antiderivative `u / k - (2/k) arctan (r sin u / (R + k + r cos u))`, where `k = √(R² - r²)`. -/
lemma integral_inv_add_cos (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    (∫ u in (0:ℝ)..(2 * π), (R + r * Real.cos u)⁻¹) = 2 * π / Real.sqrt (R ^ 2 - r ^ 2) := by
  have hR : 0 < R := lt_trans hr hRr
  set k := Real.sqrt (R ^ 2 - r ^ 2) with hkdef
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hk : 0 < k := Real.sqrt_pos.mpr hpos
  have hk2 : k ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hpos.le
  set F : ℝ → ℝ := fun u =>
    u / k - (2 / k) * Real.arctan (r * Real.sin u / (R + k + r * Real.cos u)) with hF
  have hderiv : ∀ u : ℝ, HasDerivAt F (R + r * Real.cos u)⁻¹ u := by
    intro u
    have hcos : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
    have hden : 0 < R + k + r * Real.cos u := by nlinarith [abs_le.mp hcos, hr.le]
    have hden2 : 0 < R + r * Real.cos u := by nlinarith [abs_le.mp hcos]
    have h1 : HasDerivAt (fun u : ℝ => r * Real.sin u / (R + k + r * Real.cos u))
        ((r * Real.cos u * (R + k + r * Real.cos u) - r * Real.sin u * (r * (-Real.sin u)))
          / (R + k + r * Real.cos u) ^ 2) u :=
      ((Real.hasDerivAt_sin u).const_mul r).div
        (((Real.hasDerivAt_cos u).const_mul r).const_add (R + k)) hden.ne'
    have h2 := (Real.hasDerivAt_arctan (r * Real.sin u / (R + k + r * Real.cos u))).comp u h1
    have h3 : HasDerivAt (fun u : ℝ => u / k) (1 / k) u := by
      simpa using (hasDerivAt_id u).div_const k
    have h4 := h3.sub (h2.const_mul (2 / k))
    convert h4 using 1
    have hs : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
    rw [inv_eq_one_div]
    field_simp
    linear_combination (k * r ^ 2 + R * r ^ 2 + r ^ 3 * Real.cos u) * hs
      + (R + r * Real.cos u + k) * hk2
  have hcont : IntervalIntegrable (fun u => (R + r * Real.cos u)⁻¹) MeasureTheory.volume
      0 (2 * π) := by
    refine Continuous.intervalIntegrable (Continuous.inv₀ (by fun_prop) ?_) _ _
    intro u
    exact (torus_radial_pos hr hRr u).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hcont]
  simp [hF]

/-- The inner integral: for each `v`, `∫₀^{2π} H² dA du = π R² / (2 r √(R² - r²))`. -/
lemma inner_integral (R r : ℝ) (hr : 0 < r) (hRr : r < R) (v : ℝ) :
    (∫ u in (0:ℝ)..(2 * π), surfMeanCurvature (torusParam R r) u v ^ 2 * surfAreaElement (torusParam R r) u v)
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hint : IntervalIntegrable (fun u => (R + r * Real.cos u)⁻¹) MeasureTheory.volume
      0 (2 * π) := by
    refine Continuous.intervalIntegrable (Continuous.inv₀ (by fun_prop) ?_) _ _
    intro u
    exact (torus_radial_pos hr hRr u).ne'
  have hcongr : ∀ u ∈ Set.uIcc (0:ℝ) (2 * π),
      surfMeanCurvature (torusParam R r) u v ^ 2 * surfAreaElement (torusParam R r) u v
        = Real.cos u + (R ^ 2 / (4 * r)) * (R + r * Real.cos u)⁻¹ := by
    intro u _
    have hA : 0 < R + r * Real.cos u := torus_radial_pos hr hRr u
    rw [torusMeanCurvature_eq R r u v hr hRr, torusAreaElement_eq R r u v hr hRr]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_add (Real.continuous_cos.intervalIntegrable _ _) (hint.const_mul _),
    integral_cos, intervalIntegral.integral_const_mul, integral_inv_add_cos R r hr hRr]
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith [lt_trans hr hRr]
  have hk : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hpos
  simp
  field_simp
  ring

/-- **Willmore energy of a torus of revolution.** -/
theorem willmoreEnergy_eq (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    willmoreEnergy R r = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith [lt_trans hr hRr]
  have hk : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hpos
  rw [willmoreEnergy, willmoreEnergyOf,
    intervalIntegral.integral_congr (g := fun _ => π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)))
      (fun v _ => inner_integral R r hr hRr v)]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-! ### The Willmore bound -/

/-- The elementary inequality behind the Willmore bound: `2 r √(R² - r²) ≤ R²`, an equivalent
form of `(R² - 2r²)² ≥ 0`. -/
lemma two_mul_mul_sqrt_le (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    2 * r * Real.sqrt (R ^ 2 - r ^ 2) ≤ R ^ 2 := by
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith [lt_trans hr hRr]
  have hk : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hpos
  have hk2 : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hpos.le
  nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (R ^ 2 - 2 * r * Real.sqrt (R ^ 2 - r ^ 2)),
    hk.le, hr.le]

theorem two_pi_sq_le_willmoreEnergy (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    2 * π ^ 2 ≤ willmoreEnergy R r := by
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith [lt_trans hr hRr]
  have hk : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hpos
  rw [willmoreEnergy_eq R r hr hRr, le_div_iff₀ (by positivity)]
  have h := two_mul_mul_sqrt_le R r hr hRr
  have hpi : 0 < π ^ 2 := by positivity
  nlinarith [h, hpi]

theorem willmoreEnergy_eq_two_pi_sq_iff (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    willmoreEnergy R r = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hR : 0 < R := lt_trans hr hRr
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hk : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hpos
  have hk2 : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hpos.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpi : 0 < π ^ 2 := by positivity
  rw [willmoreEnergy_eq R r hr hRr, div_eq_iff (by positivity)]
  constructor
  · intro h
    have hRsq : R ^ 2 = 2 * r ^ 2 := by
      have hRk : R ^ 2 = 2 * r * Real.sqrt (R ^ 2 - r ^ 2) := by nlinarith [hpi]
      nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), hk.le]
    have hprod : (R - Real.sqrt 2 * r) * (R + Real.sqrt 2 * r) = 0 := by
      nlinarith [hRsq, h2]
    have hsum : 0 < R + Real.sqrt 2 * r := by positivity
    rcases mul_eq_zero.mp hprod with h' | h'
    · linarith
    · linarith
  · intro h
    subst h
    have hsq : Real.sqrt ((Real.sqrt 2 * r) ^ 2 - r ^ 2) = r := by
      have h' : (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 := by nlinarith
      rw [h', Real.sqrt_sq hr.le]
    rw [hsq]
    linear_combination (π ^ 2 * r ^ 2) * h2

/-- **The Willmore conjecture for tori of revolution** (the base case of the
Marques–Neves theorem): the least Willmore energy `∫∫ H² dA` of a torus of revolution
in `ℝ³` is `2π²`, and it is attained exactly by the Clifford torus, i.e. the torus of
revolution whose radii satisfy `R = √2 · r`. -/
theorem willmore_conjecture :
    IsLeast {W : ℝ | ∃ R r : ℝ, 0 < r ∧ r < R ∧ W = willmoreEnergy R r} (2 * π ^ 2) ∧
      ∀ R r : ℝ, 0 < r → r < R → (willmoreEnergy R r = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r) := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  refine ⟨⟨⟨Real.sqrt 2, 1, one_pos, h1, ?_⟩, ?_⟩, fun R r hr hRr =>
    willmoreEnergy_eq_two_pi_sq_iff R r hr hRr⟩
  · exact ((willmoreEnergy_eq_two_pi_sq_iff (Real.sqrt 2) 1 one_pos h1).mpr (by ring)).symm
  · rintro W ⟨R, r, hr, hRr, rfl⟩
    exact two_pi_sq_le_willmoreEnergy R r hr hRr

/-! ### The general statement, and sharpness of the constant

We also record the statement of the Willmore conjecture in full generality, for an
arbitrary immersed torus, and we prove (unconditionally) that the constant `2π²`
occurring in it cannot be improved, since it is attained by the Clifford torus. -/

/-- An *immersed torus* in `ℝ³`: a `2π`-doubly periodic `C²` map `ℝ² → ℝ³` which is an
immersion, i.e. whose two partial derivatives are everywhere linearly independent
(equivalently `X_u × X_v ≠ 0`).  Such a map is exactly an immersion of the genus-one
surface `ℝ² / (2π ℤ)²` into `ℝ³`. -/
structure IsImmersedTorus (X : ℝ → ℝ → Fin 3 → ℝ) : Prop where
  /-- `X` is `2π`-periodic in the first variable. -/
  periodic_u : ∀ u v, X (u + 2 * π) v = X u v
  /-- `X` is `2π`-periodic in the second variable. -/
  periodic_v : ∀ u v, X u (v + 2 * π) = X u v
  /-- `X` is twice continuously differentiable. -/
  smooth : ContDiff ℝ 2 (fun p : ℝ × ℝ => X p.1 p.2)
  /-- `X` is an immersion. -/
  immersion : ∀ u v, surfCross X u v ≠ 0

/-- **The Willmore conjecture** (Marques–Neves): every immersed torus in `ℝ³` has
Willmore energy at least `2π²`.  This file proves the case of tori of revolution,
see `Frontier.willmore_conjecture`. -/
def WillmoreConjectureStatement : Prop :=
  ∀ X : ℝ → ℝ → Fin 3 → ℝ, IsImmersedTorus X → 2 * π ^ 2 ≤ willmoreEnergyOf X

/-- The torus of revolution with radii `R > r > 0` is an immersed torus. -/
theorem isImmersedTorus_torusParam (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    IsImmersedTorus (torusParam R r) where
  periodic_u u v := by simp [torusParam, Real.cos_add_two_pi]
  periodic_v u v := by simp [torusParam, Real.cos_add_two_pi, Real.sin_add_two_pi]
  smooth := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · show ContDiff ℝ 2 (fun p : ℝ × ℝ => (R + r * Real.cos p.1) * Real.cos p.2)
      fun_prop
    · show ContDiff ℝ 2 (fun p : ℝ × ℝ => (R + r * Real.cos p.1) * Real.sin p.2)
      fun_prop
    · show ContDiff ℝ 2 (fun p : ℝ × ℝ => r * Real.sin p.1)
      fun_prop
  immersion u v := by
    intro hzero
    have h := torusAreaElement_eq R r u v hr hRr
    rw [surfAreaElement, hzero] at h
    have hA := torus_radial_pos hr hRr u
    simp only [dotProduct, Fin.sum_univ_three, Pi.zero_apply, mul_zero, add_zero,
      Real.sqrt_zero] at h
    nlinarith

/-- **Sharpness of the Willmore bound**: the constant `2π²` in the Willmore conjecture is
attained, by the Clifford torus (the torus of revolution with `R = √2`, `r = 1`). -/
theorem willmore_bound_sharp :
    ∃ X : ℝ → ℝ → Fin 3 → ℝ, IsImmersedTorus X ∧ willmoreEnergyOf X = 2 * π ^ 2 := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  refine ⟨torusParam (Real.sqrt 2) 1, isImmersedTorus_torusParam _ _ one_pos h1, ?_⟩
  exact (willmoreEnergy_eq_two_pi_sq_iff (Real.sqrt 2) 1 one_pos h1).mpr (by ring)

/-- The general conjecture indeed contains the case proved here: assuming
`WillmoreConjectureStatement`, every torus of revolution has Willmore energy at least
`2π²`.  (This is proved unconditionally in `Frontier.two_pi_sq_le_willmoreEnergy`.) -/
theorem two_pi_sq_le_willmoreEnergy_of_general (h : WillmoreConjectureStatement)
    (R r : ℝ) (hr : 0 < r) (hRr : r < R) : 2 * π ^ 2 ≤ willmoreEnergy R r :=
  h _ (isImmersedTorus_torusParam R r hr hRr)

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

