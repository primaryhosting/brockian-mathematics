/- (Lean 4 requires `import` to be the first command, so this header is a plain block comment.)
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ContDiff

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

namespace Math2

open MeasureTheory

/-! ## Conformal metrics on the plane

We work with a smooth conformal factor `F : ℝ² → ℝ` and the Riemannian metric
`g = e^{2F} (dx² + dy²)`.  Its Gauss curvature is `K = -e^{-2F} Δ F` and its area element is
`e^{2F} dx dy`, so that the curvature density `K · e^{2F}` is exactly `-Δ F`.
-/

/-- Partial derivative in the `x`-direction of a function on the plane. -/
noncomputable def dX (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => fderiv ℝ F p (1, 0)

/-- Partial derivative in the `y`-direction of a function on the plane. -/
noncomputable def dY (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => fderiv ℝ F p (0, 1)

/-- The flat Laplacian `∂²/∂x² + ∂²/∂y²`. -/
noncomputable def lapl (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => dX (dX F) p + dY (dY F) p

/-- The Gauss curvature of the conformal Riemannian metric `e^{2F} (dx² + dy²)` on the plane. -/
noncomputable def gaussCurvature (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => -Real.exp (-(2 * F p)) * lapl F p

/-- The Riemannian area density of `e^{2F} (dx² + dy²)` with respect to Lebesgue measure. -/
noncomputable def areaDensity (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => Real.exp (2 * F p)

/-! ## Smoothness and calculus of the partial derivatives -/

lemma contDiff_dX {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dX F) :=
  (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp (hF.fderiv_right (by simp))

lemma contDiff_dY {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dY F) :=
  (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).contDiff.comp (hF.fderiv_right (by simp))

lemma hasDerivAt_dX {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (x y : ℝ) :
    HasDerivAt (fun s => F (s, y)) (dX F (x, y)) x := by
  have hd : HasFDerivAt F (fderiv ℝ F (x, y)) (x, y) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hd.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

lemma hasDerivAt_dY {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (x y : ℝ) :
    HasDerivAt (fun t => F (x, t)) (dY F (x, y)) y := by
  have hd : HasFDerivAt F (fderiv ℝ F (x, y)) (x, y) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hd.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

/-- If `F` is `1`-periodic in `x`, so is its `x`-partial derivative. -/
lemma dX_periodic {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hx : ∀ p : ℝ × ℝ, F (p.1 + 1, p.2) = F p) (x y : ℝ) :
    dX F (x + 1, y) = dX F (x, y) := by
  have h1 : HasDerivAt (fun s => F (s, y)) (dX F (x + 1, y)) (x + 1) := hasDerivAt_dX hF (x + 1) y
  have h2 : HasDerivAt (fun s => F (s + 1, y)) (dX F (x + 1, y)) x := by
    simpa using h1.comp x ((hasDerivAt_id x).add_const 1)
  have h3 : (fun s => F (s + 1, y)) = fun s => F (s, y) := by
    funext s; exact hx (s, y)
  rw [h3] at h2
  exact h2.unique (hasDerivAt_dX hF x y)

/-- If `F` is `1`-periodic in `y`, so is its `y`-partial derivative. -/
lemma dY_periodic {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hy : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) (x y : ℝ) :
    dY F (x, y + 1) = dY F (x, y) := by
  have h1 : HasDerivAt (fun t => F (x, t)) (dY F (x, y + 1)) (y + 1) := hasDerivAt_dY hF x (y + 1)
  have h2 : HasDerivAt (fun t => F (x, t + 1)) (dY F (x, y + 1)) y := by
    simpa using h1.comp y ((hasDerivAt_id y).add_const 1)
  have h3 : (fun t => F (x, t + 1)) = fun t => F (x, t) := by
    funext t; exact hy (x, t)
  rw [h3] at h2
  exact h2.unique (hasDerivAt_dY hF x y)

/-! ## Integration over a fundamental domain -/

/-- Fubini's theorem for a continuous function on the unit square. -/
lemma swap_unit_square (G : ℝ × ℝ → ℝ) (hG : Continuous G) :
    ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, G (x, y) =
      ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, G (x, y) := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  simp only [intervalIntegral.integral_of_le h01]
  have hint : Integrable (Function.uncurry fun (x : ℝ) (y : ℝ) => G (x, y))
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : IntegrableOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) (volume.prod volume) :=
      hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hc.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-- The integral of `∂²F/∂x²` over a period in `x` vanishes. -/
lemma integral_dX_dX_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hx : ∀ p : ℝ × ℝ, F (p.1 + 1, p.2) = F p) (y : ℝ) :
    ∫ x in (0:ℝ)..1, dX (dX F) (x, y) = 0 := by
  have hcont : Continuous fun x : ℝ => dX (dX F) (x, y) :=
    (contDiff_dX (contDiff_dX hF)).continuous.comp (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => dX F (s, y)) (f' := fun s => dX (dX F) (s, y)) (a := 0) (b := 1)
    (fun s _ => hasDerivAt_dX (contDiff_dX hF) s y) (hcont.intervalIntegrable 0 1)
  rw [h]
  have hp := dX_periodic hF hx 0 y
  rw [zero_add] at hp
  simp [hp]

/-- The integral of `∂²F/∂y²` over a period in `y` vanishes. -/
lemma integral_dY_dY_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hy : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) (x : ℝ) :
    ∫ y in (0:ℝ)..1, dY (dY F) (x, y) = 0 := by
  have hcont : Continuous fun y : ℝ => dY (dY F) (x, y) :=
    (contDiff_dY (contDiff_dY hF)).continuous.comp (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => dY F (x, t)) (f' := fun t => dY (dY F) (x, t)) (a := 0) (b := 1)
    (fun t _ => hasDerivAt_dY (contDiff_dY hF) x t) (hcont.intervalIntegrable 0 1)
  rw [h]
  have hp := dY_periodic hF hy x 0
  rw [zero_add] at hp
  simp [hp]

/-- The curvature density of the conformal metric is minus the flat Laplacian of `F`. -/
lemma gaussCurvature_mul_areaDensity (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    gaussCurvature F p * areaDensity F p = -dX (dX F) p + -dY (dY F) p := by
  have hexp : Real.exp (-(2 * F p)) * Real.exp (2 * F p) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [gaussCurvature, areaDensity, lapl]
  calc -Real.exp (-(2 * F p)) * (dX (dX F) p + dY (dY F) p) * Real.exp (2 * F p)
      = -((dX (dX F) p + dY (dY F) p) *
          (Real.exp (-(2 * F p)) * Real.exp (2 * F p))) := by ring
    _ = -dX (dX F) p + -dY (dY F) p := by rw [hexp]; ring

/-! ## The theorem -/

/-- **Chern–Gauss–Bonnet on the two-dimensional torus** `T² = ℝ²/ℤ²`.

Let `F : ℝ² → ℝ` be smooth and doubly periodic with period lattice `ℤ²`; equivalently, `F` is a
smooth function on the torus `T²`.  It defines the Riemannian metric `g = e^{2F}(dx² + dy²)` on
`T²`, whose Gauss curvature is `K = -e^{-2F} Δ F` and whose Riemannian area element is
`e^{2F} dx dy`.  The theorem states that the total curvature of `g`, integrated over the
fundamental domain `[0,1]²`, equals `2π · χ(T²)`, where the Euler characteristic of the
two-torus is `χ(T²) = 0`.

In dimension two the Chern–Gauss–Bonnet integrand (the Pfaffian of the curvature form divided
by `(2π)^n`) is exactly `K / (2π)` times the area form, so this is the Chern–Gauss–Bonnet
formula for the closed even-dimensional manifold `T²` equipped with an arbitrary conformal
metric. -/
theorem chern_gauss_bonnet (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hx : ∀ p : ℝ × ℝ, F (p.1 + 1, p.2) = F p)
    (hy : ∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) :
    ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
      = 2 * Real.pi * (0 : ℝ) := by
  have hcontXX : Continuous (dX (dX F)) := (contDiff_dX (contDiff_dX hF)).continuous
  have hcontYY : Continuous (dY (dY F)) := (contDiff_dY (contDiff_dY hF)).continuous
  have inner : ∀ x : ℝ, ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
      = ∫ y in (0:ℝ)..1, -dX (dX F) (x, y) := by
    intro x
    have h1 : IntervalIntegrable (fun y : ℝ => -dX (dX F) (x, y)) volume 0 1 :=
      ((hcontXX.comp (by fun_prop)).neg).intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun y : ℝ => -dY (dY F) (x, y)) volume 0 1 :=
      ((hcontYY.comp (by fun_prop)).neg).intervalIntegrable 0 1
    calc ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
        = ∫ y in (0:ℝ)..1, (-dX (dX F) (x, y) + -dY (dY F) (x, y)) := by
          simp only [gaussCurvature_mul_areaDensity]
      _ = (∫ y in (0:ℝ)..1, -dX (dX F) (x, y)) + ∫ y in (0:ℝ)..1, -dY (dY F) (x, y) :=
          intervalIntegral.integral_add h1 h2
      _ = ∫ y in (0:ℝ)..1, -dX (dX F) (x, y) := by
          have hzero : ∫ y in (0:ℝ)..1, -dY (dY F) (x, y) = 0 := by
            rw [intervalIntegral.integral_neg, integral_dY_dY_eq_zero hF hy x, neg_zero]
          rw [hzero, add_zero]
  calc ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, gaussCurvature F (x, y) * areaDensity F (x, y)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, -dX (dX F) (x, y) := by
        simp only [inner]
    _ = ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, -dX (dX F) (x, y) :=
        swap_unit_square (fun p => -dX (dX F) p) hcontXX.neg
    _ = 2 * Real.pi * (0 : ℝ) := by
        have hzero : ∀ y : ℝ, ∫ x in (0:ℝ)..1, -dX (dX F) (x, y) = 0 := by
          intro y
          rw [intervalIntegral.integral_neg, integral_dX_dX_eq_zero hF hx y, neg_zero]
        simp [hzero]

/-! ## Sanity check: the round sphere

Stereographic projection identifies `S² ∖ {pt}` with `ℝ²`, and transports the round metric of the
unit sphere to the conformal metric `e^{2F}(dx²+dy²)` with `F = log 2 - log (1 + x² + y²)`.
We check that the definitions above indeed return Gauss curvature identically `1` for this
conformal factor, which is the defining property of the unit round sphere. -/

/-- The conformal factor of the round unit sphere in stereographic coordinates. -/
noncomputable def sphereFactor : ℝ × ℝ → ℝ :=
  fun p => Real.log 2 - Real.log (1 + p.1 ^ 2 + p.2 ^ 2)

lemma sphere_denom_pos (p : ℝ × ℝ) : 0 < 1 + p.1 ^ 2 + p.2 ^ 2 := by positivity

lemma contDiff_sphereFactor : ContDiff ℝ ∞ sphereFactor :=
  ContDiff.sub contDiff_const (ContDiff.log (by fun_prop) fun p => (sphere_denom_pos p).ne')

lemma dX_sphereFactor : dX sphereFactor = fun p => -(2 * p.1) / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  funext p
  obtain ⟨x, y⟩ := p
  have h1 : HasDerivAt (fun s : ℝ => sphereFactor (s, y)) (-(2 * x) / (1 + x ^ 2 + y ^ 2)) x := by
    have hD : HasDerivAt (fun s : ℝ => 1 + s ^ 2 + y ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (1 : ℝ)).add_const (y ^ 2)
    have hne : (1 + x ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (by positivity)
    have h := (hD.log hne).const_sub (Real.log 2)
    convert h using 1
    field_simp
  exact (h1.unique (hasDerivAt_dX contDiff_sphereFactor x y)).symm

lemma dY_sphereFactor : dY sphereFactor = fun p => -(2 * p.2) / (1 + p.1 ^ 2 + p.2 ^ 2) := by
  funext p
  obtain ⟨x, y⟩ := p
  have h1 : HasDerivAt (fun t : ℝ => sphereFactor (x, t)) (-(2 * y) / (1 + x ^ 2 + y ^ 2)) y := by
    have hD : HasDerivAt (fun t : ℝ => 1 + x ^ 2 + t ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (1 + x ^ 2)
    have hne : (1 + x ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (by positivity)
    have h := (hD.log hne).const_sub (Real.log 2)
    convert h using 1
    field_simp
  exact (h1.unique (hasDerivAt_dY contDiff_sphereFactor x y)).symm

lemma dX_dX_sphereFactor (x y : ℝ) :
    dX (dX sphereFactor) (x, y) = (2 * x ^ 2 - 2 * y ^ 2 - 2) / (1 + x ^ 2 + y ^ 2) ^ 2 := by
  have hcd : ContDiff ℝ ∞ (dX sphereFactor) := contDiff_dX contDiff_sphereFactor
  have h1 : HasDerivAt (fun s : ℝ => dX sphereFactor (s, y))
      ((2 * x ^ 2 - 2 * y ^ 2 - 2) / (1 + x ^ 2 + y ^ 2) ^ 2) x := by
    rw [dX_sphereFactor]
    have hD : HasDerivAt (fun s : ℝ => 1 + s ^ 2 + y ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (1 : ℝ)).add_const (y ^ 2)
    have hne : (1 + x ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (by positivity)
    have hnum : HasDerivAt (fun s : ℝ => -(2 * s)) (-2 : ℝ) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).neg
    have h := hnum.div hD hne
    simp only at h ⊢
    convert h using 1
    field_simp
    ring
  exact (h1.unique (hasDerivAt_dX hcd x y)).symm

lemma dY_dY_sphereFactor (x y : ℝ) :
    dY (dY sphereFactor) (x, y) = (2 * y ^ 2 - 2 * x ^ 2 - 2) / (1 + x ^ 2 + y ^ 2) ^ 2 := by
  have hcd : ContDiff ℝ ∞ (dY sphereFactor) := contDiff_dY contDiff_sphereFactor
  have h1 : HasDerivAt (fun t : ℝ => dY sphereFactor (x, t))
      ((2 * y ^ 2 - 2 * x ^ 2 - 2) / (1 + x ^ 2 + y ^ 2) ^ 2) y := by
    rw [dY_sphereFactor]
    have hD : HasDerivAt (fun t : ℝ => 1 + x ^ 2 + t ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (1 + x ^ 2)
    have hne : (1 + x ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (by positivity)
    have hnum : HasDerivAt (fun t : ℝ => -(2 * t)) (-2 : ℝ) y := by
      simpa using ((hasDerivAt_id y).const_mul (2 : ℝ)).neg
    have h := hnum.div hD hne
    simp only at h ⊢
    convert h using 1
    field_simp
    ring
  exact (h1.unique (hasDerivAt_dY hcd x y)).symm

lemma lapl_sphereFactor (p : ℝ × ℝ) : lapl sphereFactor p = -4 / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 := by
  obtain ⟨x, y⟩ := p
  simp only [lapl, dX_dX_sphereFactor, dY_dY_sphereFactor]
  have hne : ((1 + x ^ 2 + y ^ 2) : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The stereographic conformal factor really is that of the unit round sphere: the resulting
Gauss curvature is constantly `1`. -/
theorem gaussCurvature_sphereFactor (p : ℝ × ℝ) : gaussCurvature sphereFactor p = 1 := by
  have hexp : Real.exp (-(2 * sphereFactor p)) = (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 / 4 := by
    unfold sphereFactor
    rw [show -(2 * (Real.log 2 - Real.log (1 + p.1 ^ 2 + p.2 ^ 2)))
          = 2 * Real.log (1 + p.1 ^ 2 + p.2 ^ 2) - 2 * Real.log 2 by ring, Real.exp_sub,
      show (2:ℝ) * Real.log (1 + p.1 ^ 2 + p.2 ^ 2) = Real.log ((1 + p.1 ^ 2 + p.2 ^ 2) ^ 2) by
        rw [Real.log_pow]; push_cast; ring,
      show (2:ℝ) * Real.log 2 = Real.log ((2:ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity), Real.exp_log (by norm_num)]
    norm_num
  have hne : ((1 + p.1 ^ 2 + p.2 ^ 2) : ℝ) ^ 2 ≠ 0 := by positivity
  simp only [gaussCurvature, hexp, lapl_sphereFactor]
  field_simp

/-! ## Chern–Gauss–Bonnet for the round sphere

Stereographic coordinates cover `S²` up to a single point, a set of measure zero, so the total
curvature of the round sphere is computed by an integral over all of `ℝ²`.  It equals
`4π = 2π · χ(S²)`, the Chern–Gauss–Bonnet formula for the closed surface `S²`. -/

lemma integral_Ioi_radial : ∫ x in Set.Ioi (0:ℝ), 4 * x / (1 + x ^ 2) ^ 2 = 2 := by
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun r : ℝ => -2 / (1 + r ^ 2)) (4 * x / (1 + x ^ 2) ^ 2) x := by
    intro x _
    have hD : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (hasDerivAt_const x (-2 : ℝ)).div hD hne
    convert h using 1
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun r : ℝ => -2 / (1 + r ^ 2)) (Set.Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    exact Continuous.div continuous_const (by fun_prop) fun r => by positivity
  have hlim : Filter.Tendsto (fun r : ℝ => -2 / (1 + r ^ 2)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop (by norm_num))
  have hpos : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ 4 * x / (1 + x ^ 2) ^ 2 := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    positivity
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  norm_num

lemma integral_plane_inv_sq : ∫ p : ℝ × ℝ, (4:ℝ) / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 = 4 * Real.pi := by
  rw [← integral_comp_polarCoord_symm (fun p : ℝ × ℝ => (4:ℝ) / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2)]
  have hcongr : ∀ p ∈ polarCoord.target,
      p.1 • ((4:ℝ) / (1 + (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) ^ 2)
        = (fun r : ℝ => 4 * r / (1 + r ^ 2) ^ 2) p.1 * (fun _ : ℝ => (1:ℝ)) p.2 := by
    intro p _
    have hs : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
    rw [hs]
    have hsc : 1 + (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = 1 + p.1 ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq p.2]
    simp only [hsc, smul_eq_mul, mul_one]
    ring
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr, polarCoord_target,
    Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => 4 * r / (1 + r ^ 2) ^ 2) (fun _ : ℝ => (1:ℝ)) (Set.Ioi 0)
    (Set.Ioo (-Real.pi) Real.pi)
  rw [h, integral_Ioi_radial, setIntegral_const, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by nlinarith [Real.pi_pos]), smul_eq_mul]
  ring

/-- **Chern–Gauss–Bonnet for the round two-sphere.**  In stereographic coordinates the round
metric of `S²` is the conformal metric with factor `sphereFactor`, and its total curvature is
`2π · χ(S²) = 2π · 2 = 4π`. -/
theorem chern_gauss_bonnet_sphere :
    ∫ p : ℝ × ℝ, gaussCurvature sphereFactor p * areaDensity sphereFactor p
      = 2 * Real.pi * 2 := by
  have hint : ∀ p : ℝ × ℝ, gaussCurvature sphereFactor p * areaDensity sphereFactor p
      = 4 / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2 := by
    intro p
    have h1 := gaussCurvature_mul_areaDensity sphereFactor p
    have h2 := lapl_sphereFactor p
    simp only [lapl] at h2
    rw [show (-4 : ℝ) / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2
      = -(4 / (1 + p.1 ^ 2 + p.2 ^ 2) ^ 2) by ring] at h2
    rw [h1]
    linarith
  simp only [hint]
  rw [integral_plane_inv_sq]
  ring

end Math2

