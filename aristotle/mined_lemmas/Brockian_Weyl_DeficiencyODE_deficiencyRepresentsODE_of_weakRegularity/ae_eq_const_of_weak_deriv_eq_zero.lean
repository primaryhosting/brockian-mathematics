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

import Brockian.Weyl.TestFunction

/-!
# The du Bois-Reymond lemmas

A locally integrable function whose distributional derivative vanishes is almost everywhere
constant; a locally integrable function whose distributional second derivative vanishes is
almost everywhere affine.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-! ## The du Bois-Reymond lemmas -/

/-- **du Bois-Reymond lemma.**  A locally integrable function whose distributional derivative
vanishes is almost everywhere constant. -/

theorem ae_eq_const_of_weak_deriv_eq_zero {v : ℝ → ℂ} (hv : LocallyIntegrable v volume)
    (h : ∀ ψ : ℝ → ℝ, IsTestFunction ψ → ∫ x, ((deriv ψ x : ℝ) : ℂ) * v x = 0) :
    ∃ c : ℂ, v =ᵐ[volume] fun _ => c := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_testFunction_integral_eq_one
  set c : ℂ := ∫ x, ((χ x : ℝ) : ℂ) * v x with hc
  refine ⟨c, ?_⟩
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (v x - c) = 0 := by
    intro ψ h1 h2
    have hψ : IsTestFunction ψ := ⟨h1, h2⟩
    set m : ℝ := ∫ x, ψ x with hm
    set ψ₀ : ℝ → ℝ := fun x => ψ x - m * χ x with hψ₀
    have hψ₀T : IsTestFunction ψ₀ :=
      ⟨h1.sub (contDiff_const.mul hχ.1), h2.sub (hχ.2.mul_left)⟩
    have h0 : ∫ x, ψ₀ x = 0 := by
      rw [hψ₀]
      rw [integral_sub hψ.integrable ((hχ.integrable.const_mul m))]
      rw [integral_const_mul, hχ1, ← hm]
      ring
    obtain ⟨Φ, hΦ, hdΦ⟩ := hψ₀T.exists_primitive h0
    have hkey := h Φ hΦ
    rw [hdΦ] at hkey
    -- expand
    have hmchi : IsTestFunction (fun x => m * χ x) :=
      ⟨contDiff_const.mul hχ.1, hχ.2.mul_left⟩
    have hint1 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * v x) :=
      integrable_ofReal_mul_of_locallyIntegrable hψ hv
    have hint2 : Integrable (fun x => ((m * χ x : ℝ) : ℂ) * v x) :=
      integrable_ofReal_mul_of_locallyIntegrable hmchi hv
    have hsplit : ∫ x, ((ψ₀ x : ℝ) : ℂ) * v x
        = (∫ x, ((ψ x : ℝ) : ℂ) * v x) - ∫ x, ((m * χ x : ℝ) : ℂ) * v x := by
      rw [← integral_sub hint1 hint2]
      apply integral_congr_ae
      filter_upwards with x
      simp only [hψ₀, Complex.ofReal_sub]
      ring
    have hmc : ∫ x, ((m * χ x : ℝ) : ℂ) * v x = (m : ℂ) * c := by
      rw [hc, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Complex.ofReal_mul]
      ring
    rw [hsplit, hmc] at hkey
    -- conclude
    have hcm : ∫ x, ψ x • (v x - c) = (∫ x, ((ψ x : ℝ) : ℂ) * v x) - (m : ℂ) * c := by
      have hint3 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * c) :=
        integrable_ofReal_mul hψ continuous_const
      have : ∫ x, ψ x • (v x - c)
          = (∫ x, ((ψ x : ℝ) : ℂ) * v x) - ∫ x, ((ψ x : ℝ) : ℂ) * c := by
        rw [← integral_sub hint1 hint3]
        apply integral_congr_ae
        filter_upwards with x
        rw [Complex.real_smul]
        ring
      rw [this]
      congr 1
      rw [integral_mul_const, integral_complex_ofReal, ← hm]
    rw [hcm, hkey]
  have hli : LocallyIntegrable (fun x => v x - c) volume :=
    hv.sub (continuous_const.locallyIntegrable)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli key
  filter_upwards [hae] with x hx
  simpa [sub_eq_zero] using hx

/-- **du Bois-Reymond lemma, second order.**  A locally integrable function whose distributional
second derivative vanishes is almost everywhere affine. -/
