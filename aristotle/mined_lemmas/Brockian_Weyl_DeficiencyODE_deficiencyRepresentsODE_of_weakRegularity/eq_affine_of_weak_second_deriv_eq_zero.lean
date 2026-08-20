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

theorem eq_affine_of_weak_second_deriv_eq_zero {v : ℝ → ℂ} (hv : Continuous v)
    (h : ∀ φ : ℝ → ℝ, IsTestFunction φ → ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * v x = 0) :
    ∃ a b : ℂ, ∀ x, v x = a + b * x := by
  obtain ⟨a, b, hab⟩ := ae_eq_affine_of_weak_second_deriv_eq_zero hv.locallyIntegrable h
  refine ⟨a, b, fun x => congrFun ((hv.ae_eq_iff_eq (μ := volume) (by fun_prop)).mp hab) x⟩

end Brockian.Weyl.DeficiencyODE

import Mathlib

/-!
# Test functions on the line

Basic API for smooth compactly supported functions `ℝ → ℝ`, used to formulate distributional
(weak) solutions of second order ODEs.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-- A test function on `ℝ`: smooth and compactly supported. -/
