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

theorem hasCompactSupport_ofReal {ψ : ℝ → ℝ} (h : HasCompactSupport ψ) :
    HasCompactSupport (fun x => ((ψ x : ℝ) : ℂ)) := by
  refine HasCompactSupport.intro (K := tsupport ψ) h fun x hx => ?_
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- A test function times a continuous function is integrable. -/
