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

theorem ae_eq_affine_of_weak_second_deriv_eq_zero {v : ℝ → ℂ}
    (hv : LocallyIntegrable v volume)
    (h : ∀ φ : ℝ → ℝ, IsTestFunction φ → ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * v x = 0) :
    ∃ a b : ℂ, v =ᵐ[volume] fun x => a + b * x := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_testFunction_integral_eq_one
  set k : ℂ := ∫ x, ((deriv χ x : ℝ) : ℂ) * v x with hk
  have hstep : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x, ((deriv ψ x : ℝ) : ℂ) * (v x + k * x) = 0 := by
    intro ψ hψ
    set m : ℝ := ∫ x, ψ x with hm
    have hmchi : IsTestFunction (fun x => m * χ x) := ⟨contDiff_const.mul hχ.1, hχ.2.mul_left⟩
    set ψ₀ : ℝ → ℝ := fun x => ψ x - m * χ x with hψ₀
    have hψ₀T : IsTestFunction ψ₀ := ⟨hψ.1.sub hmchi.1, hψ.2.sub hmchi.2⟩
    have h0 : ∫ x, ψ₀ x = 0 := by
      rw [hψ₀, integral_sub hψ.integrable (hχ.integrable.const_mul m), integral_const_mul,
        hχ1, ← hm]
      ring
    obtain ⟨Φ, hΦ, hdΦ⟩ := hψ₀T.exists_primitive h0
    have hdψ : ∀ x, deriv ψ x = deriv (deriv Φ) x + m * deriv χ x := by
      intro x
      have hda : HasDerivAt (fun y => ψ y - m * χ y) (deriv ψ x - m * deriv χ x) x :=
        ((hψ.differentiable x).hasDerivAt).sub
          (HasDerivAt.const_mul m ((hχ.differentiable x).hasDerivAt))
      have h1 : deriv ψ₀ x = deriv ψ x - m * deriv χ x := by rw [hψ₀]; exact hda.deriv
      rw [hdΦ, h1]; ring
    have hd1 : IsTestFunction (deriv ψ) := isTestFunction_deriv hψ
    have i1 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * v x) :=
      integrable_ofReal_mul_of_locallyIntegrable hd1 hv
    have i2 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * (k * (x : ℂ))) :=
      integrable_ofReal_mul hd1 (by fun_prop)
    have hsum : (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * (v x + k * x))
        = fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * v x + ((deriv ψ x : ℝ) : ℂ) * (k * (x : ℂ)) := by
      funext x; ring
    -- the first integral
    have hA : ∫ x, ((deriv ψ x : ℝ) : ℂ) * v x = (m : ℂ) * k := by
      have e1 : (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * v x)
          = fun x : ℝ => ((deriv (deriv Φ) x : ℝ) : ℂ) * v x
              + (m : ℂ) * (((deriv χ x : ℝ) : ℂ) * v x) := by
        funext x; rw [hdψ x]; push_cast; ring
      have j1 : Integrable (fun x => ((deriv (deriv Φ) x : ℝ) : ℂ) * v x) :=
        integrable_ofReal_mul_of_locallyIntegrable
          (isTestFunction_deriv (isTestFunction_deriv hΦ)) hv
      have j2 : Integrable (fun x => (m : ℂ) * (((deriv χ x : ℝ) : ℂ) * v x)) :=
        (integrable_ofReal_mul_of_locallyIntegrable (isTestFunction_deriv hχ) hv).const_mul _
      rw [e1, integral_add j1 j2, h Φ hΦ, integral_const_mul, ← hk]
      ring
    -- the second integral
    have hB : ∫ x, ((deriv ψ x : ℝ) : ℂ) * (x : ℂ) = -(m : ℂ) := by
      have := integral_deriv_mul (f := fun x : ℝ => ((ψ x : ℝ) : ℂ))
        (f' := fun x : ℝ => ((deriv ψ x : ℝ) : ℂ)) (g := fun x : ℝ => (x : ℂ))
        (g' := fun _ => (1 : ℂ)) (fun x => hψ.hasDerivAt_ofReal x)
        (fun x => by simpa using (Complex.ofRealCLM.hasDerivAt (x := x)))
        hd1.continuous_ofReal continuous_const (hasCompactSupport_ofReal hψ.2)
      rw [this, hm, ← integral_complex_ofReal]
      simp
    rw [hsum, integral_add i1 i2, hA]
    have hBk : ∫ x, ((deriv ψ x : ℝ) : ℂ) * (k * (x : ℂ))
        = k * ∫ x, ((deriv ψ x : ℝ) : ℂ) * (x : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hBk, hB]
    ring
  obtain ⟨c, hcv⟩ := ae_eq_const_of_weak_deriv_eq_zero
    (v := fun x => v x + k * x) (hv.add (by fun_prop : Continuous fun x : ℝ => k * (x : ℂ)
      ).locallyIntegrable) hstep
  refine ⟨c, -k, ?_⟩
  filter_upwards [hcv] with x hx
  have hx' : v x + k * x = c := hx
  linear_combination hx'

/-! ## Continuous versions -/

/-- A continuous function whose distributional derivative vanishes is constant. -/
