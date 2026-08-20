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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

theorem weak_solution_eq_zero (V₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) {u : ℝ → ℂ}
    (hu : MemLp u 2 volume)
    (hweak : ∀ f : ℝ → ℂ, IsTestFunction f →
      ∫ x, (starRingEnd ℂ) (u x) * (schrodingerExpr V₀ f x - z * f x) = 0) :
    u =ᵐ[volume] 0 := by
  set F : ℝ → ℂ := fun x => (starRingEnd ℂ) (u x) with hFdef
  have hFmem : MemLp F 2 volume := by
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hu.1, ?_⟩
    have hnorm : eLpNorm F 2 volume = eLpNorm u 2 volume := by
      apply eLpNorm_congr_norm_ae; filter_upwards with x; simp [hFdef]
    rw [hnorm]; exact hu.2
  have hFloc : LocallyIntegrable F volume := hFmem.locallyIntegrable one_le_two
  set L := ContinuousLinearMap.mul ℝ ℂ with hL
  -- For every test function `ρ`, the smooth function `F ⋆ ρ` is a bounded solution of the
  -- ODE `y'' = (V₀ - z) y`, hence vanishes identically.
  have key : ∀ ρ : ℝ → ℂ, IsTestFunction ρ → ∀ t : ℝ, (F ⋆[L, volume] ρ) t = 0 := by
    rintro ρ ⟨hρs, hρc⟩ t₀
    have hρ1 : Differentiable ℝ ρ := hρs.differentiable (by simp)
    have hρs' : ContDiff ℝ (⊤ : ℕ∞) (deriv ρ) := by simpa using hρs.iterate_deriv 1
    have hρ1' : Differentiable ℝ (deriv ρ) := hρs'.differentiable (by simp)
    have hd1 : deriv (F ⋆[L, volume] ρ) = F ⋆[L, volume] (deriv ρ) := by
      funext t
      exact (hρc.hasDerivAt_convolution_right L hFloc
        (hρs.of_le (by exact_mod_cast le_top)) t).deriv
    have hd2 : deriv (deriv (F ⋆[L, volume] ρ)) = F ⋆[L, volume] (deriv (deriv ρ)) := by
      rw [hd1]
      funext t
      exact ((hρc.deriv).hasDerivAt_convolution_right L hFloc
        (hρs'.of_le (by exact_mod_cast le_top)) t).deriv
    have hy2 : ContDiff ℝ 2 (F ⋆[L, volume] ρ) :=
      (hρc.contDiff_convolution_right L hFloc hρs).of_le ENat.LEInfty.out
    have hode : ∀ t : ℝ, deriv (deriv (F ⋆[L, volume] ρ)) t
        = ((V₀ : ℂ) - z) * (F ⋆[L, volume] ρ) t := by
      intro t
      have htest : IsTestFunction (fun x => ρ (t - x)) :=
        ⟨hρs.comp (contDiff_const.sub contDiff_id),
         hρc.comp_homeomorph (Homeomorph.subLeft t)⟩
      have hw := hweak _ htest
      have hsec : deriv (deriv (fun x => ρ (t - x))) = fun x => deriv (deriv ρ) (t - x) := by
        rw [deriv_comp_const_sub hρ1 t, deriv.fun_neg', deriv_comp_const_sub hρ1' t]
        funext x; simp
      simp only [schrodingerExpr, hsec] at hw
      have hint1 : Integrable (fun x => F x * deriv (deriv ρ) (t - x)) volume := by
        apply integrable_mul_test hFloc
        · exact (hρs'.continuous_deriv (by exact_mod_cast le_top)).comp
            (continuous_const.sub continuous_id)
        · exact (hρc.deriv.deriv).comp_homeomorph (Homeomorph.subLeft t)
      have hint2 : Integrable (fun x => F x * ρ (t - x)) volume := by
        apply integrable_mul_test hFloc
        · exact hρ1.continuous.comp (continuous_const.sub continuous_id)
        · exact hρc.comp_homeomorph (Homeomorph.subLeft t)
      have hsplit : (∫ x, (-(F x * deriv (deriv ρ) (t - x))
            + ((V₀ : ℂ) - z) * (F x * ρ (t - x)))) = 0 := by
        rw [← hw]; congr 1; funext x; ring
      have hadd := integral_add (μ := volume)
        (f := fun x => -(F x * deriv (deriv ρ) (t - x)))
        (g := fun x => ((V₀ : ℂ) - z) * (F x * ρ (t - x))) hint1.neg (hint2.const_mul _)
      rw [hadd, integral_neg, integral_const_mul] at hsplit
      have e1 : (F ⋆[L, volume] (deriv (deriv ρ))) t = ∫ x, F x * deriv (deriv ρ) (t - x) := rfl
      have e2 : (F ⋆[L, volume] ρ) t = ∫ x, F x * ρ (t - x) := rfl
      rw [hd2, e1, e2]
      linear_combination -hsplit
    have hbdd : ∀ t : ℝ, ‖(F ⋆[L, volume] ρ) t‖
        ≤ (∫ x, ‖u x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (∫ x, ‖ρ x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
      fun t => conv_bounded hu hρ1.continuous hρc t
    exact bounded_ode_solution_eq_zero (by simp [Complex.sub_im, hz]) hy2 hode hbdd t₀
  have hFae : ∀ᵐ x ∂volume, F x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hFloc
    intro g hg hgc
    have hρtest : IsTestFunction (fun x => ((g (-x) : ℝ) : ℂ)) := by
      constructor
      · exact Complex.ofRealCLM.contDiff.comp (hg.comp contDiff_neg)
      · apply HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) _ (by simp)
        exact hgc.comp_homeomorph (Homeomorph.neg ℝ)
    have hk := key _ hρtest 0
    have e : (F ⋆[L, volume] (fun x => ((g (-x) : ℝ) : ℂ))) 0 = ∫ x, F x * (g x : ℂ) := by
      simp [convolution, hL]
    rw [e] at hk
    rw [← hk]
    congr 1
    funext x
    simp [Complex.real_smul, mul_comm]
  filter_upwards [hFae] with x hx
  have hux : u x = (starRingEnd ℂ) (F x) := by simp [hFdef]
  rw [hux, hx]; simp

/-! ## Linearity of the minimal operator -/

