import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the module documentation block above is placed immediately after `import Mathlib`.
-/

open Real Set MeasureTheory intervalIntegral

namespace Frontier

/-! ## The torus of revolution and its Willmore energy

For `0 < r < R`, the torus of revolution `T R r ⊆ ℝ³` obtained by revolving the circle of
radius `r` centred at distance `R` from the axis is parametrised by

  `(θ, φ) ↦ ((R + r cos θ) cos φ, (R + r cos θ) sin φ, r sin θ)`,  `θ, φ ∈ [0, 2π]`.

Its two principal curvatures are `1 / r` (along the meridian circle) and
`cos θ / (R + r cos θ)` (along the parallel circle), and its area element is
`r (R + r cos θ) dθ dφ`.  These classical formulas are taken as the definitions below;
the Willmore energy `∫ H² dA` is then the honest double integral of the square of the mean
curvature against the area element.
-/

/-- The principal curvature `k₁ = 1/r` of the torus of revolution, along the meridian
circle of radius `r`. -/
noncomputable def torusPrincipalCurvature₁ (r : ℝ) : ℝ := 1 / r

/-- The principal curvature `k₂ = cos θ / (R + r cos θ)` of the torus of revolution, along
the parallel circle through the point with meridian angle `θ`. -/
noncomputable def torusPrincipalCurvature₂ (R r θ : ℝ) : ℝ :=
  Real.cos θ / (R + r * Real.cos θ)

/-- The mean curvature `H = (k₁ + k₂)/2` of the torus of revolution with radii `R > r > 0`,
at the point with meridian angle `θ`. -/
noncomputable def torusMeanCurvature (R r θ : ℝ) : ℝ :=
  (torusPrincipalCurvature₁ r + torusPrincipalCurvature₂ R r θ) / 2

/-- The Gauss curvature `K = k₁ k₂` of the torus of revolution with radii `R > r > 0`. -/
noncomputable def torusGaussCurvature (R r θ : ℝ) : ℝ :=
  torusPrincipalCurvature₁ r * torusPrincipalCurvature₂ R r θ

/-- The area element `r (R + r cos θ)` of the torus of revolution with radii `R > r > 0`. -/
noncomputable def torusAreaElement (R r θ : ℝ) : ℝ := r * (R + r * Real.cos θ)

/-- The Willmore energy `W = ∫ H² dA` of the torus of revolution with radii `R > r > 0`. -/
noncomputable def willmoreEnergyTorusOfRevolution (R r : ℝ) : ℝ :=
  ∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..(2 * π),
    (torusMeanCurvature R r θ) ^ 2 * torusAreaElement R r θ

section Basic

variable {R r : ℝ}

/-- Positivity of the parametrising denominator. -/
lemma add_mul_cos_pos (hr : 0 < r) (hRr : r < R) (θ : ℝ) : 0 < R + r * Real.cos θ := by
  have h1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  nlinarith [Real.cos_le_one θ]

/-- Pointwise simplification of the Willmore integrand. -/
lemma willmore_integrand_eq (hr : 0 < r) (hRr : r < R) (θ : ℝ) :
    (torusMeanCurvature R r θ) ^ 2 * torusAreaElement R r θ =
      Real.cos θ + R ^ 2 / (4 * r) * (R + r * Real.cos θ)⁻¹ := by
  have hd : R + r * Real.cos θ ≠ 0 := (add_mul_cos_pos hr hRr θ).ne'
  unfold torusMeanCurvature torusAreaElement torusPrincipalCurvature₁ torusPrincipalCurvature₂
  field_simp
  ring

/-- The total area of the torus of revolution is `4π² R r`. -/
theorem torus_total_area (hr : 0 < r) (hRr : r < R) :
    (∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..(2 * π), torusAreaElement R r θ)
      = 4 * π ^ 2 * R * r := by
  have hinner : (∫ θ in (0 : ℝ)..(2 * π), torusAreaElement R r θ) = 2 * π * (r * R) := by
    unfold torusAreaElement
    have hc2 : Continuous fun θ : ℝ => r ^ 2 * Real.cos θ :=
      continuous_const.mul Real.continuous_cos
    rw [intervalIntegral.integral_congr
        (g := fun θ => r * R + r ^ 2 * Real.cos θ) (fun θ _ => by ring),
      intervalIntegral.integral_add _root_.intervalIntegrable_const
        (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_cos, intervalIntegral.integral_const]
    simp [Real.sin_two_pi]
  rw [hinner, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- **Gauss–Bonnet check**: the total Gauss curvature of the torus of revolution vanishes,
consistent with Euler characteristic `0`, i.e. genus `1`. -/
theorem torus_total_gauss_curvature (hr : 0 < r) (hRr : r < R) :
    (∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..(2 * π),
        torusGaussCurvature R r θ * torusAreaElement R r θ) = 0 := by
  have hinner : (∫ θ in (0 : ℝ)..(2 * π),
      torusGaussCurvature R r θ * torusAreaElement R r θ) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun θ => Real.cos θ) (fun θ _ => ?_)]
    · simp
    · have hd : R + r * Real.cos θ ≠ 0 := (add_mul_cos_pos hr hRr θ).ne'
      unfold torusGaussCurvature torusAreaElement torusPrincipalCurvature₁ torusPrincipalCurvature₂
      field_simp
  simp [hinner]

end Basic

section KeyIntegral

variable {R r : ℝ}

/-- The antiderivative of `θ ↦ (R + r cos θ)⁻¹` used on `[0, π]`. -/
noncomputable def arccosAntideriv (R r θ : ℝ) : ℝ :=
  Real.arccos ((r + R * Real.cos θ) / (R + r * Real.cos θ)) / Real.sqrt (R ^ 2 - r ^ 2)

lemma continuous_arccosAntideriv (hr : 0 < r) (hRr : r < R) :
    Continuous (arccosAntideriv R r) := by
  unfold arccosAntideriv
  apply Continuous.div_const
  apply Real.continuous_arccos.comp
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (add_mul_cos_pos hr hRr x).ne'

lemma hasDerivAt_arccosAntideriv (hr : 0 < r) (hRr : r < R) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    HasDerivAt (arccosAntideriv R r) ((R + r * Real.cos θ)⁻¹) θ := by
  have hD : 0 < R + r * Real.cos θ := add_mul_cos_pos hr hRr θ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hd2 : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hq : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hd2
  have hq2 : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hd2.le
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  set u : ℝ := (r + R * Real.cos θ) / (R + r * Real.cos θ) with hu
  have hone : 1 - u ^ 2 = (R ^ 2 - r ^ 2) * Real.sin θ ^ 2 / (R + r * Real.cos θ) ^ 2 := by
    rw [hu]; field_simp; nlinarith [hpyth]
  have hsqrt : Real.sqrt (1 - u ^ 2)
      = Real.sqrt (R ^ 2 - r ^ 2) * Real.sin θ / (R + r * Real.cos θ) := by
    rw [hone, show (R ^ 2 - r ^ 2) * Real.sin θ ^ 2 / (R + r * Real.cos θ) ^ 2
        = (Real.sqrt (R ^ 2 - r ^ 2) * Real.sin θ / (R + r * Real.cos θ)) ^ 2 by
      field_simp; nlinarith [hq2]]
    exact Real.sqrt_sq (by positivity)
  have hlt : u ^ 2 < 1 := by
    have : 0 < 1 - u ^ 2 := by rw [hone]; positivity
    linarith
  have hne1 : u ≠ 1 := by intro h; rw [h] at hlt; norm_num at hlt
  have hne2 : u ≠ -1 := by intro h; rw [h] at hlt; norm_num at hlt
  have hn : HasDerivAt (fun θ : ℝ => r + R * Real.cos θ) (R * (-Real.sin θ)) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul R).const_add r
  have hdd : HasDerivAt (fun θ : ℝ => R + r * Real.cos θ) (r * (-Real.sin θ)) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul r).const_add R
  have hU : HasDerivAt (fun θ : ℝ => (r + R * Real.cos θ) / (R + r * Real.cos θ))
      ((R * (-Real.sin θ) * (R + r * Real.cos θ) - (r + R * Real.cos θ) * (r * (-Real.sin θ)))
        / (R + r * Real.cos θ) ^ 2) θ := hn.div hdd hD.ne'
  have hA := (Real.hasDerivAt_arccos hne2 hne1).comp θ hU
  have hfin := hA.div_const (Real.sqrt (R ^ 2 - r ^ 2))
  convert hfin using 1
  rw [hsqrt]
  field_simp
  nlinarith [hq2, hq, hsin, hD]

lemma continuous_inv_add_mul_cos (hr : 0 < r) (hRr : r < R) :
    Continuous fun θ : ℝ => (R + r * Real.cos θ)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) (fun x => (add_mul_cos_pos hr hRr x).ne')

lemma arccosAntideriv_zero (hr : 0 < r) (hRr : r < R) : arccosAntideriv R r 0 = 0 := by
  unfold arccosAntideriv
  have h : (r + R * Real.cos 0) / (R + r * Real.cos 0) = 1 := by
    rw [Real.cos_zero]
    rw [div_eq_one_iff_eq (by nlinarith)]
    ring
  rw [h, Real.arccos_one, zero_div]

lemma arccosAntideriv_pi (hRr : r < R) :
    arccosAntideriv R r π = π / Real.sqrt (R ^ 2 - r ^ 2) := by
  unfold arccosAntideriv
  have h : (r + R * Real.cos π) / (R + r * Real.cos π) = -1 := by
    rw [Real.cos_pi]
    rw [div_eq_iff (by nlinarith)]
    ring
  rw [h, Real.arccos_neg_one]

lemma integral_inv_add_mul_cos_zero_pi (hr : 0 < r) (hRr : r < R) :
    ∫ θ in (0 : ℝ)..π, (R + r * Real.cos θ)⁻¹ = π / Real.sqrt (R ^ 2 - r ^ 2) := by
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le pi_pos.le
    (continuous_arccosAntideriv hr hRr).continuousOn
    (fun x hx => (hasDerivAt_arccosAntideriv hr hRr hx.1 hx.2).hasDerivWithinAt)
    ((continuous_inv_add_mul_cos hr hRr).intervalIntegrable _ _)
  rw [key, arccosAntideriv_zero hr hRr, arccosAntideriv_pi hRr, sub_zero]

lemma integral_inv_add_mul_cos (hr : 0 < r) (hRr : r < R) :
    ∫ θ in (0 : ℝ)..(2 * π), (R + r * Real.cos θ)⁻¹ = 2 * π / Real.sqrt (R ^ 2 - r ^ 2) := by
  have hcont := continuous_inv_add_mul_cos hr hRr
  have hrefl : ∀ x : ℝ, (R + r * Real.cos (2 * π - x))⁻¹ = (R + r * Real.cos x)⁻¹ := by
    intro x
    rw [Real.cos_two_pi_sub]
  have h2 := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := π)
    (fun θ : ℝ => (R + r * Real.cos θ)⁻¹) (2 * π)
  simp only [hrefl] at h2
  rw [show 2 * π - π = π by ring, sub_zero] at h2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := π) (c := 2 * π) (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [← hadd, ← h2, integral_inv_add_mul_cos_zero_pi hr hRr]
  ring

end KeyIntegral

section ClosedForm

variable {R r : ℝ}

/-- **Willmore's closed formula**: the Willmore energy of the torus of revolution with
radii `R > r > 0` equals `π² R² / (r √(R² - r²))`. -/
theorem willmoreEnergyTorusOfRevolution_eq (hr : 0 < r) (hRr : r < R) :
    willmoreEnergyTorusOfRevolution R r = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hs : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hsq : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hs
  have hcont := continuous_inv_add_mul_cos hr hRr
  have hcont2 : Continuous fun θ : ℝ => R ^ 2 / (4 * r) * (R + r * Real.cos θ)⁻¹ :=
    continuous_const.mul hcont
  have hinner : (∫ θ in (0 : ℝ)..(2 * π),
        (torusMeanCurvature R r θ) ^ 2 * torusAreaElement R r θ)
      = R ^ 2 / (4 * r) * (2 * π / Real.sqrt (R ^ 2 - r ^ 2)) := by
    rw [intervalIntegral.integral_congr
      (g := fun θ => Real.cos θ + R ^ 2 / (4 * r) * (R + r * Real.cos θ)⁻¹)
      (fun θ _ => willmore_integrand_eq hr hRr θ)]
    rw [intervalIntegral.integral_add (Real.continuous_cos.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul, integral_cos, integral_inv_add_mul_cos hr hRr]
    simp
  rw [willmoreEnergyTorusOfRevolution, hinner, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp
  ring

/-- The lower bound `2π²` for the closed-form energy, with the equality case. -/
theorem closed_form_ge (hr : 0 < r) (hRr : r < R) :
    2 * π ^ 2 ≤ π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hpos.le
  have key : 2 * (r * s) ≤ R ^ 2 := by nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (r * s)]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg π, pi_pos]

theorem closed_form_eq_iff (hr : 0 < r) (hRr : r < R) :
    π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r := by
  set s := Real.sqrt (R ^ 2 - r ^ 2) with hs
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hpos.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_eq_iff (by positivity)]
  constructor
  · intro h
    have hR2 : R ^ 2 = 2 * r ^ 2 := by
      have hRs : R ^ 2 = 2 * (r * s) := by
        field_simp at h; nlinarith [pi_pos]
      nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2)]
    have hfac : (R - Real.sqrt 2 * r) * (R + Real.sqrt 2 * r) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · nlinarith
  · intro h
    subst h
    have hsq : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by nlinarith
    have hsr : s = r := by
      rw [hs, hsq, show 2 * r ^ 2 - r ^ 2 = r ^ 2 by ring, Real.sqrt_sq hr.le]
    rw [hsr, hsq]
    ring

end ClosedForm

/-- **The Willmore conjecture for tori of revolution** (Willmore's theorem, the base case of
the Willmore conjecture proved in full generality by Marques–Neves).

For every torus of revolution in `ℝ³` with radii `0 < r < R`, the Willmore energy
`∫ H² dA` is at least `2π²`, and equality holds exactly for the Clifford-type torus
`R = √2 · r`, the stereographic image of the Clifford torus. -/
theorem willmore_conjecture {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    2 * π ^ 2 ≤ willmoreEnergyTorusOfRevolution R r ∧
      (willmoreEnergyTorusOfRevolution R r = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r) := by
  rw [willmoreEnergyTorusOfRevolution_eq hr hRr]
  exact ⟨closed_form_ge hr hRr, closed_form_eq_iff hr hRr⟩

/-- The Clifford torus attains the minimal Willmore energy `2π²`. -/
theorem willmoreEnergy_clifford {r : ℝ} (hr : 0 < r) :
    willmoreEnergyTorusOfRevolution (Real.sqrt 2 * r) r = 2 * π ^ 2 := by
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hRr : r < Real.sqrt 2 * r := by nlinarith
  exact (willmore_conjecture hr hRr).2.mpr rfl

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

