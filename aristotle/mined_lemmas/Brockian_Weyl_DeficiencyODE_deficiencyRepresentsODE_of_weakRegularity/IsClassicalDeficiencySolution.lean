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

theorem IsClassicalDeficiencySolution.isWeakDeficiencySolution {q : ℝ → ℂ} {z : ℂ} {u : ℝ → ℂ}
    (h : IsClassicalDeficiencySolution q z u) : IsWeakDeficiencySolution q z u := by
  obtain ⟨hu2, hode⟩ := h
  obtain ⟨hdiff, -, hC1⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) u from hu2)
  have hu1 : ∀ x, HasDerivAt u (deriv u x) x := fun x => (hdiff x).hasDerivAt
  have hu1' : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x =>
    ((contDiff_one_iff_deriv.mp hC1).1 x).hasDerivAt
  have hcu1 : Continuous (deriv u) := hC1.continuous
  have hcu2 : Continuous (deriv (deriv u)) := (contDiff_one_iff_deriv.mp hC1).2
  intro φ hφ
  have h1 : ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * u x = -∫ x, ((deriv φ x : ℝ) : ℂ) * deriv u x :=
    integral_deriv_mul (fun x => (isTestFunction_deriv hφ).hasDerivAt_ofReal x) hu1
      (isTestFunction_deriv (isTestFunction_deriv hφ)).continuous_ofReal hcu1
      (hasCompactSupport_ofReal (isTestFunction_deriv hφ).2)
  have h2 : ∫ x, ((deriv φ x : ℝ) : ℂ) * deriv u x
      = -∫ x, ((φ x : ℝ) : ℂ) * deriv (deriv u) x :=
    integral_deriv_mul (fun x => hφ.hasDerivAt_ofReal x) hu1'
      (isTestFunction_deriv hφ).continuous_ofReal hcu2 (hasCompactSupport_ofReal hφ.2)
  rw [h1, h2, neg_neg]
  have hpt : ∀ x : ℝ, ((φ x : ℝ) : ℂ) * deriv (deriv u) x
      = ((φ x : ℝ) : ℂ) * ((q x - z) * u x) := fun x => by rw [hode x]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end Brockian.Weyl.DeficiencyODE

