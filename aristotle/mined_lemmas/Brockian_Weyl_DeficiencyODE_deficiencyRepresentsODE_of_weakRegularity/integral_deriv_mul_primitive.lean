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

theorem integral_deriv_mul_primitive {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    {g : ℝ → ℂ} (hg : LocallyIntegrable g volume) :
    ∫ x, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0:ℝ)..x, g t) = -∫ x, ((ψ x : ℝ) : ℂ) * g x := by
  set H : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, g t with hH
  have hHc : Continuous H :=
    intervalIntegral.continuous_primitive (locallyIntegrable_intervalIntegrable hg) 0
  have hint1 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * H x) volume :=
    integrable_ofReal_mul (isTestFunction_deriv hψ) hHc
  have hint2 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * g x) volume :=
    integrable_ofReal_mul_of_locallyIntegrable hψ hg
  -- it suffices to compare the images under the real-linear maps `re` and `im`
  have key : ∀ L : ℂ →L[ℝ] ℝ, (∀ (r : ℝ) (w : ℂ), L ((r : ℂ) * w) = r * L w) →
      L (∫ x, ((deriv ψ x : ℝ) : ℂ) * H x) = L (-∫ x, ((ψ x : ℝ) : ℂ) * g x) := by
    intro L hL
    have hLg : LocallyIntegrable (fun x => L (g x)) volume := by
      intro x
      obtain ⟨s, hs, hint⟩ := hg x
      exact ⟨s, hs, (L.integrable_comp hint)⟩
    have hLH : ∀ x, L (H x) = ∫ t in (0:ℝ)..x, L (g t) := fun x =>
      (L.intervalIntegral_comp_comm (locallyIntegrable_intervalIntegrable hg 0 x)).symm
    have p1 : ∀ x : ℝ, L (((deriv ψ x : ℝ) : ℂ) * H x)
        = deriv ψ x * (∫ t in (0:ℝ)..x, L (g t)) := fun x => by rw [hL, hLH]
    have p2 : ∀ x : ℝ, L (((ψ x : ℝ) : ℂ) * g x) = ψ x * L (g x) := fun x => by rw [hL]
    have e1 : L (∫ x, ((deriv ψ x : ℝ) : ℂ) * H x)
        = ∫ x, deriv ψ x * (∫ t in (0:ℝ)..x, L (g t)) := by
      rw [← L.integral_comp_comm hint1]
      exact integral_congr_ae (Filter.Eventually.of_forall p1)
    have e2 : L (∫ x, ((ψ x : ℝ) : ℂ) * g x) = ∫ x, ψ x * L (g x) := by
      rw [← L.integral_comp_comm hint2]
      exact integral_congr_ae (Filter.Eventually.of_forall p2)
    rw [e1, map_neg, e2, integral_deriv_mul_primitive_real hψ hLg]
  refine Complex.ext ?_ ?_
  · simpa using key Complex.reCLM (fun r w => by simp)
  · simpa using key Complex.imCLM (fun r w => by simp)

end Brockian.Weyl.DeficiencyODE

import Brockian.Weyl.DuBoisReymond

/-!
# Deficiency elements of a Sturm–Liouville expression solve the ODE

This file contains the elliptic-regularity ("deficiency represents ODE") statement in one
dimension: any *distributional* solution of the Weyl deficiency equation

`u'' = (q - z) u`

is, after modification on a null set, a classical `C²` solution.  No regularity whatsoever is
assumed on `u` beyond local integrability (which is needed for the distributional formulation
to make sense at all); in particular, the deficiency elements of the minimal operator, which
are a priori only `L²` functions, are genuine solutions of the ordinary differential equation.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-- `u` is a distributional (weak) solution of the deficiency equation `u'' = (q - z) u`. -/
