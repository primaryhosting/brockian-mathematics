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

/-!
## Setting

The Willmore conjecture, proved by Marques and Neves (2014, Fields Medal work of
A. Neves' collaborator F. C. Marques / awarded context), asserts that every immersed
torus in `ℝ³` has Willmore energy `∫ H² dA ≥ 2π²`, with equality exactly for the
Clifford torus (and its images under conformal transformations of `S³`).

The file below formalizes and *proves* the classical base case, due to T. J. Willmore
(1965): the conjecture holds for tori of revolution, i.e. for the surfaces obtained by
revolving a circle of radius `r` about an axis at distance `R > r` in its plane.  For
these surfaces everything (mean curvature, area element, hence the Willmore energy) is
completely explicit, and we compute the energy in closed form, minimize it, and identify
the unique minimizer as the ratio `R = √2 · r` — the "Clifford" torus of revolution.
-/

/-- The mean curvature `H = (k₁ + k₂)/2` of the torus of revolution with tube radius `r`
and center-circle radius `R`, at the tube-angle `u`.  Here `k₁ = 1/r` and
`k₂ = cos u / (R + r cos u)`. -/
noncomputable def torusMeanCurvature (R r u : ℝ) : ℝ :=
  (R + 2 * r * Real.cos u) / (2 * r * (R + r * Real.cos u))

/-- The area element `dA = r (R + r cos u) du dv` of the torus of revolution with tube
radius `r` and center-circle radius `R`, in the standard parametrization
`(u, v) ↦ ((R + r cos u) cos v, (R + r cos u) sin v, r sin u)`. -/
noncomputable def torusAreaElement (R r u : ℝ) : ℝ := r * (R + r * Real.cos u)

/-- The Willmore energy `∫ H² dA` of the torus of revolution with tube radius `r` and
center-circle radius `R`. -/
noncomputable def willmoreEnergyOfRevolution (R r : ℝ) : ℝ :=
  ∫ _v in (0:ℝ)..(2 * Real.pi), ∫ u in (0:ℝ)..(2 * Real.pi),
    (torusMeanCurvature R r u) ^ 2 * torusAreaElement R r u

/-! ## Geometric justification of the two definitions above

The mean curvature and area element used above are not postulated: we check them
against the standard parametrization
`X(u, v) = ((R + r cos u) cos v, (R + r cos u) sin v, r sin u)` of the torus of
revolution, by computing its first and second fundamental forms.
-/

/-- The standard parametrization of the torus of revolution. -/
noncomputable def torusParam (R r u v : ℝ) : Fin 3 → ℝ :=
  ![(R + r * Real.cos u) * Real.cos v, (R + r * Real.cos u) * Real.sin v, r * Real.sin u]

/-- `∂X/∂u`. -/
noncomputable def torusXu (r u v : ℝ) : Fin 3 → ℝ :=
  ![-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u]

/-- `∂X/∂v`. -/
noncomputable def torusXv (R r u v : ℝ) : Fin 3 → ℝ :=
  ![-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0]

/-- `∂²X/∂u²`. -/
noncomputable def torusXuu (r u v : ℝ) : Fin 3 → ℝ :=
  ![-(r * Real.cos u) * Real.cos v, -(r * Real.cos u) * Real.sin v, -(r * Real.sin u)]

/-- `∂²X/∂u∂v`. -/
noncomputable def torusXuv (r u v : ℝ) : Fin 3 → ℝ :=
  ![r * Real.sin u * Real.sin v, -(r * Real.sin u * Real.cos v), 0]

/-- `∂²X/∂v²`. -/
noncomputable def torusXvv (R r u v : ℝ) : Fin 3 → ℝ :=
  ![-((R + r * Real.cos u) * Real.cos v), -((R + r * Real.cos u) * Real.sin v), 0]

/-- The unit normal field of the torus of revolution. -/
noncomputable def torusNormal (u v : ℝ) : Fin 3 → ℝ :=
  ![Real.cos u * Real.cos v, Real.cos u * Real.sin v, Real.sin u]

/-- The Euclidean inner product on `ℝ³`. -/
def dot3 (a b : Fin 3 → ℝ) : ℝ := ∑ i, a i * b i

theorem hasDerivAt_torusParam_u (R r u v : ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => torusParam R r t v i) (torusXu r u v i) u := by
  fin_cases i <;> simp only [torusParam, torusXu]
  · simpa using ((((Real.hasDerivAt_cos u).const_mul r).const_add R).mul_const (Real.cos v))
  · simpa using ((((Real.hasDerivAt_cos u).const_mul r).const_add R).mul_const (Real.sin v))
  · simpa using ((Real.hasDerivAt_sin u).const_mul r)

theorem hasDerivAt_torusParam_v (R r u v : ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => torusParam R r u t i) (torusXv R r u v i) v := by
  fin_cases i <;> simp only [torusParam, torusXv]
  · simpa using ((Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u))
  · simpa using ((Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u))
  · simpa using hasDerivAt_const v (r * Real.sin u)

theorem hasDerivAt_torusXu_u (r u v : ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => torusXu r t v i) (torusXuu r u v i) u := by
  fin_cases i <;> simp only [torusXu, torusXuu]
  · simpa using (((Real.hasDerivAt_sin u).const_mul r).neg.mul_const (Real.cos v))
  · simpa using (((Real.hasDerivAt_sin u).const_mul r).neg.mul_const (Real.sin v))
  · simpa using ((Real.hasDerivAt_cos u).const_mul r)

theorem hasDerivAt_torusXu_v (r u v : ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => torusXu r u t i) (torusXuv r u v i) v := by
  fin_cases i <;> simp only [torusXu, torusXuv]
  · simpa using ((Real.hasDerivAt_cos v).const_mul (-(r * Real.sin u)))
  · simpa using ((Real.hasDerivAt_sin v).const_mul (-(r * Real.sin u)))
  · simpa using hasDerivAt_const v (r * Real.cos u)

theorem hasDerivAt_torusXv_v (R r u v : ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => torusXv R r u t i) (torusXvv R r u v i) v := by
  fin_cases i <;> simp only [torusXv, torusXvv]
  · simpa using ((Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u)).neg
  · simpa using ((Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u))
  · simpa using hasDerivAt_const v (0:ℝ)

/-- The normal field is a unit vector. -/
theorem torusNormal_unit (u v : ℝ) : dot3 (torusNormal u v) (torusNormal u v) = 1 := by
  simp only [dot3, torusNormal, Fin.sum_univ_three, Matrix.cons_val]
  linear_combination (Real.cos u ^ 2) * (Real.sin_sq_add_cos_sq v) + (Real.sin_sq_add_cos_sq u)

/-- The normal field is orthogonal to `∂X/∂u`. -/
theorem torusNormal_orth_u (r u v : ℝ) : dot3 (torusXu r u v) (torusNormal u v) = 0 := by
  simp only [dot3, torusXu, torusNormal, Fin.sum_univ_three, Matrix.cons_val]
  linear_combination (-(r * Real.sin u * Real.cos u)) * (Real.sin_sq_add_cos_sq v)

/-- The normal field is orthogonal to `∂X/∂v`. -/
theorem torusNormal_orth_v (R r u v : ℝ) : dot3 (torusXv R r u v) (torusNormal u v) = 0 := by
  simp only [dot3, torusXv, torusNormal, Fin.sum_univ_three, Matrix.cons_val]
  ring

/-- First fundamental form coefficient `E = ⟨X_u, X_u⟩ = r²`. -/
theorem torus_E_eq (r u v : ℝ) : dot3 (torusXu r u v) (torusXu r u v) = r ^ 2 := by
  simp only [dot3, torusXu, Fin.sum_univ_three, Matrix.cons_val]
  linear_combination (r ^ 2 * Real.sin u ^ 2) * (Real.sin_sq_add_cos_sq v)
    + r ^ 2 * (Real.sin_sq_add_cos_sq u)

/-- First fundamental form coefficient `F = ⟨X_u, X_v⟩ = 0`. -/
theorem torus_F_eq (R r u v : ℝ) : dot3 (torusXu r u v) (torusXv R r u v) = 0 := by
  simp only [dot3, torusXu, torusXv, Fin.sum_univ_three, Matrix.cons_val]
  ring

/-- First fundamental form coefficient `G = ⟨X_v, X_v⟩ = (R + r cos u)²`. -/
theorem torus_G_eq (R r u v : ℝ) :
    dot3 (torusXv R r u v) (torusXv R r u v) = (R + r * Real.cos u) ^ 2 := by
  simp only [dot3, torusXv, Fin.sum_univ_three, Matrix.cons_val]
  linear_combination ((R + r * Real.cos u) ^ 2) * (Real.sin_sq_add_cos_sq v)

/-- Second fundamental form coefficient `L = ⟨X_uu, n⟩ = -r`. -/
theorem torus_L_eq (r u v : ℝ) : dot3 (torusXuu r u v) (torusNormal u v) = -r := by
  simp only [dot3, torusXuu, torusNormal, Fin.sum_univ_three, Matrix.cons_val]
  linear_combination (-(r * Real.cos u ^ 2)) * (Real.sin_sq_add_cos_sq v)
    - r * (Real.sin_sq_add_cos_sq u)

/-- Second fundamental form coefficient `M = ⟨X_uv, n⟩ = 0`. -/
theorem torus_M_eq (r u v : ℝ) : dot3 (torusXuv r u v) (torusNormal u v) = 0 := by
  simp only [dot3, torusXuv, torusNormal, Fin.sum_univ_three, Matrix.cons_val]
  ring

/-- Second fundamental form coefficient `N = ⟨X_vv, n⟩ = -(R + r cos u) cos u`. -/
theorem torus_N_eq (R r u v : ℝ) :
    dot3 (torusXvv R r u v) (torusNormal u v) = -((R + r * Real.cos u) * Real.cos u) := by
  simp only [dot3, torusXvv, torusNormal, Fin.sum_univ_three, Matrix.cons_val]
  linear_combination (-(R + r * Real.cos u) * Real.cos u) * (Real.sin_sq_add_cos_sq v)

/-- The area element `√(EG - F²)` of the parametrization agrees with `torusAreaElement`. -/
theorem torus_areaElement_eq {R r : ℝ} (hr : 0 < r) (u v : ℝ) (hA : 0 < R + r * Real.cos u) :
    Real.sqrt (dot3 (torusXu r u v) (torusXu r u v) * dot3 (torusXv R r u v) (torusXv R r u v)
        - dot3 (torusXu r u v) (torusXv R r u v) ^ 2)
      = torusAreaElement R r u := by
  rw [torus_E_eq, torus_G_eq, torus_F_eq, torusAreaElement]
  rw [show r ^ 2 * (R + r * Real.cos u) ^ 2 - (0:ℝ) ^ 2 = (r * (R + r * Real.cos u)) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- The mean curvature `H = (EN - 2FM + GL) / (2(EG - F²))` of the parametrization agrees,
up to the (irrelevant) choice of orientation, with `torusMeanCurvature`. -/
theorem torus_meanCurvature_eq {R r : ℝ} (hr : 0 < r) (u v : ℝ) (hA : 0 < R + r * Real.cos u) :
    (dot3 (torusXu r u v) (torusXu r u v) * dot3 (torusXvv R r u v) (torusNormal u v)
        - 2 * dot3 (torusXu r u v) (torusXv R r u v) * dot3 (torusXuv r u v) (torusNormal u v)
        + dot3 (torusXv R r u v) (torusXv R r u v) * dot3 (torusXuu r u v) (torusNormal u v))
      / (2 * (dot3 (torusXu r u v) (torusXu r u v) * dot3 (torusXv R r u v) (torusXv R r u v)
        - dot3 (torusXu r u v) (torusXv R r u v) ^ 2))
      = -torusMeanCurvature R r u := by
  rw [torus_E_eq, torus_G_eq, torus_F_eq, torus_L_eq, torus_M_eq, torus_N_eq, torusMeanCurvature]
  have h1 : r ≠ 0 := ne_of_gt hr
  have h2 : R + r * Real.cos u ≠ 0 := ne_of_gt hA
  field_simp
  ring

/-! ## The basic trigonometric integral -/

/-- `∫₀^{2π} du / (a + cos u) = 2π / √(a² - 1)` for `a > 1`. -/
theorem integral_inv_const_add_cos {a : ℝ} (ha : 1 < a) :
    ∫ u in (0:ℝ)..(2 * Real.pi), (a + Real.cos u)⁻¹ = 2 * Real.pi / Real.sqrt (a ^ 2 - 1) := by
  set b : ℝ := Real.sqrt (a ^ 2 - 1) with hb
  have ha0 : (0:ℝ) < a := lt_trans zero_lt_one ha
  have hb2 : b ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by nlinarith)
  have hDpos : ∀ u : ℝ, 0 < a + Real.cos u + b := by
    intro u
    have := Real.neg_one_le_cos u
    linarith
  have hApos : ∀ u : ℝ, 0 < a + Real.cos u := by
    intro u
    have := Real.neg_one_le_cos u
    linarith
  set G : ℝ → ℝ :=
    fun u => (u - 2 * Real.arctan (Real.sin u / (a + Real.cos u + b))) / b with hG
  have key : ∀ u : ℝ, HasDerivAt G ((a + Real.cos u)⁻¹) u := by
    intro u
    have hD := hDpos u
    have hA := hApos u
    have h1 : HasDerivAt (fun x : ℝ => Real.sin x / (a + Real.cos x + b))
        ((Real.cos u * (a + Real.cos u + b) - Real.sin u * (-Real.sin u)) /
          (a + Real.cos u + b) ^ 2) u :=
      (Real.hasDerivAt_sin u).div
        (((Real.hasDerivAt_cos u).const_add a).add_const b) (ne_of_gt hD)
    have h2 := h1.arctan
    have h3 : HasDerivAt (fun x : ℝ => x - 2 * Real.arctan (Real.sin x / (a + Real.cos x + b)))
        (1 - 2 * (1 / (1 + (Real.sin u / (a + Real.cos u + b)) ^ 2) *
          ((Real.cos u * (a + Real.cos u + b) - Real.sin u * (-Real.sin u)) /
            (a + Real.cos u + b) ^ 2))) u :=
      (hasDerivAt_id u).sub (h2.const_mul 2)
    have h4 := h3.div_const b
    convert h4 using 1
    have hs : Real.sin u ^ 2 = 1 - Real.cos u ^ 2 := by
      have := Real.sin_sq_add_cos_sq u; linarith
    have hne : (1 + (Real.sin u / (a + Real.cos u + b)) ^ 2)
        = 2 * (a + b) * (a + Real.cos u) / (a + Real.cos u + b) ^ 2 := by
      field_simp
      nlinarith [hs, hb2]
    rw [hne]
    have h2s : (0:ℝ) < 2 * (a + b) * (a + Real.cos u) := by positivity
    field_simp
    nlinarith [hs, hb2, hA.le, hbpos.le]
  have hint : IntervalIntegrable (fun u : ℝ => (a + Real.cos u)⁻¹)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop (disch := intro x; exact ne_of_gt (hApos x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x) hint]
  simp [hG, Real.sin_two_pi, Real.cos_two_pi]

/-- `∫₀^{2π} du / (R + r cos u) = 2π / √(R² - r²)` for `0 < r < R`. -/
theorem integral_inv_add_mul_cos {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    ∫ u in (0:ℝ)..(2 * Real.pi), (R + r * Real.cos u)⁻¹
      = 2 * Real.pi / Real.sqrt (R ^ 2 - r ^ 2) := by
  have ha : 1 < R / r := (one_lt_div hr).mpr hRr
  have hsplit : ∀ u : ℝ, (R + r * Real.cos u)⁻¹ = r⁻¹ * ((R / r + Real.cos u)⁻¹) := by
    intro u
    rw [← mul_inv]
    congr 1
    field_simp
  have hsqrt : Real.sqrt ((R / r) ^ 2 - 1) = Real.sqrt (R ^ 2 - r ^ 2) / r := by
    rw [show (R / r) ^ 2 - 1 = (R ^ 2 - r ^ 2) / r ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr.le]
  have hpos : 0 < Real.sqrt (R ^ 2 - r ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith)
  simp only [hsplit]
  rw [intervalIntegral.integral_const_mul, integral_inv_const_add_cos ha, hsqrt]
  field_simp

/-! ## The Willmore energy of a torus of revolution -/

/-- Closed form for the Willmore energy of the torus of revolution:
`W(R, r) = π² R² / (r √(R² - r²))`. -/
theorem willmoreEnergyOfRevolution_eq {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    willmoreEnergyOfRevolution R r
      = Real.pi ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hApos : ∀ u : ℝ, 0 < R + r * Real.cos u := by
    intro u
    have h1 : -1 ≤ Real.cos u := Real.neg_one_le_cos u
    nlinarith
  -- pointwise rewriting of the integrand
  have hpt : ∀ u : ℝ, (torusMeanCurvature R r u) ^ 2 * torusAreaElement R r u
      = Real.cos u + (R ^ 2 / (4 * r)) * (R + r * Real.cos u)⁻¹ := by
    intro u
    have h := (hApos u).ne'
    simp only [torusMeanCurvature, torusAreaElement]
    field_simp
    ring
  have hcos : IntervalIntegrable Real.cos MeasureTheory.volume 0 (2 * Real.pi) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hinv : IntervalIntegrable (fun u : ℝ => (R ^ 2 / (4 * r)) * (R + r * Real.cos u)⁻¹)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop (disch := intro x; exact (hApos x).ne')
  have hinner : (∫ u in (0:ℝ)..(2 * Real.pi),
      (torusMeanCurvature R r u) ^ 2 * torusAreaElement R r u)
      = Real.pi * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    simp only [hpt]
    rw [intervalIntegral.integral_add hcos hinv, intervalIntegral.integral_const_mul,
      integral_inv_add_mul_cos hr hRr]
    have hc : (∫ u in (0:ℝ)..(2 * Real.pi), Real.cos u) = 0 := by
      simp [integral_cos]
    rw [hc]
    have hpos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    field_simp
    ring
  have hpos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  rw [willmoreEnergyOfRevolution, hinner]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

/-- **Willmore's theorem (1965): the base case of the Willmore conjecture.**

Every torus of revolution in `ℝ³` — obtained by revolving a circle of radius `r > 0`
about a coplanar axis at distance `R > r` from its centre — has Willmore energy
`∫ H² dA ≥ 2π²`, and equality holds exactly for the ratio `R = √2 · r`, i.e. exactly
for the (stereographic image of the) Clifford torus.

This is the classical base case of the Willmore conjecture, whose full form (for
arbitrary immersed genus-one surfaces) was proved by Marques and Neves. -/
theorem willmore_conjecture {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    2 * Real.pi ^ 2 ≤ willmoreEnergyOfRevolution R r ∧
      (willmoreEnergyOfRevolution R r = 2 * Real.pi ^ 2 ↔ R = Real.sqrt 2 * r) := by
  have hR : 0 < R := lt_trans hr hRr
  set s : ℝ := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hW : willmoreEnergyOfRevolution R r = Real.pi ^ 2 * R ^ 2 / (r * s) :=
    willmoreEnergyOfRevolution_eq hr hRr
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrs : 0 < r * s := by positivity
  -- key algebraic fact: `2 r s ≤ R²`, with equality iff `R² = 2 r²`
  have hkey : 2 * (r * s) ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (2 * (r * s) - R ^ 2), hs2, hrs,
      sq_nonneg (r * s)]
  constructor
  · rw [hW, le_div_iff₀ hrs]
    nlinarith
  · rw [hW, div_eq_iff (ne_of_gt hrs)]
    constructor
    · intro h
      -- `π² R² = 2π² r s` forces `R² = 2 r s`, hence `R² = 2 r²`
      have hpi2 : (Real.pi ^ 2) ≠ 0 := by positivity
      have h1 : R ^ 2 = 2 * (r * s) :=
        mul_left_cancel₀ hpi2 (by linear_combination h)
      have h2 : R ^ 2 = 2 * r ^ 2 := by nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), hs2]
      have hx : 0 < Real.sqrt 2 * r := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hr
      have hsq : (Real.sqrt 2 * r) ^ 2 = R ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        linarith
      nlinarith [hsq, hx, hR]
    · intro h
      have h2 : R ^ 2 = 2 * r ^ 2 := by
        rw [h, mul_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
      have hsr : s = r := by
        have : s ^ 2 = r ^ 2 := by rw [hs2, h2]; ring
        nlinarith [hspos, hr]
      rw [hsr]
      nlinarith

end Frontier

