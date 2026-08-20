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

theorem eq_const_of_weak_deriv_eq_zero {v : ℝ → ℂ} (hv : Continuous v)
    (h : ∀ ψ : ℝ → ℝ, IsTestFunction ψ → ∫ x, ((deriv ψ x : ℝ) : ℂ) * v x = 0) :
    ∃ c : ℂ, ∀ x, v x = c := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_weak_deriv_eq_zero hv.locallyIntegrable h
  exact ⟨c, fun x => congrFun ((hv.ae_eq_iff_eq (μ := volume) continuous_const).mp hc) x⟩

/-- A continuous function whose distributional second derivative vanishes is affine. -/
