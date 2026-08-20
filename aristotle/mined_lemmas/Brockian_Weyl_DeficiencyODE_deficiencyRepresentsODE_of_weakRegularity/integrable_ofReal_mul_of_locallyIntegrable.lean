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

theorem integrable_ofReal_mul_of_locallyIntegrable {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    {w : ℝ → ℂ} (hw : LocallyIntegrable w volume) :
    Integrable (fun x => ((ψ x : ℝ) : ℂ) * w x) := by
  have hli : LocallyIntegrable (fun x => ((ψ x : ℝ) : ℂ) * w x) volume := by
    rw [← locallyIntegrableOn_univ] at hw ⊢
    exact hw.continuousOn_mul hψ.continuous_ofReal.continuousOn
      (IsClosed.isLocallyClosed isClosed_univ)
  have hcs : HasCompactSupport (fun x => ((ψ x : ℝ) : ℂ) * w x) :=
    (hasCompactSupport_ofReal hψ.2).mul_right
  refine (hli.integrableOn_isCompact hcs.isCompact).integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := fun y => ((ψ y : ℝ) : ℂ) * w y) hx

/-- A test function is globally Lipschitz. -/
