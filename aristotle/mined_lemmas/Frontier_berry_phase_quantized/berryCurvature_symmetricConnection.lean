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
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real Interval
open MeasureTheory Set

namespace Frontier

/-- The Berry curvature of a Berry connection `A : ℝ × ℝ → ℝ × ℝ` on a two–dimensional
parameter space: `F = ∂₁ A₂ - ∂₂ A₁`. -/

theorem berryCurvature_symmetricConnection (p : ℝ × ℝ) :
    berryCurvature symmetricConnection p = 1 := by
  have h₂ : (fun q : ℝ × ℝ => (symmetricConnection q).2) = fun q : ℝ × ℝ => q.1 / 2 := rfl
  have h₁ : (fun q : ℝ × ℝ => (symmetricConnection q).1) = fun q : ℝ × ℝ => -q.2 / 2 := rfl
  rw [berryCurvature, h₁, h₂]
  have e₂ : fderiv ℝ (fun q : ℝ × ℝ => q.1 / 2) p = (1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    have : (fun q : ℝ × ℝ => q.1 / 2) = fun q : ℝ × ℝ => (1 / 2 : ℝ) * q.1 := by
      funext q; ring
    rw [this]
    rw [fderiv_const_mul (by fun_prop) _]
    · simp [fderiv_fst]
  have e₁ : fderiv ℝ (fun q : ℝ × ℝ => -q.2 / 2) p
      = -((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    have : (fun q : ℝ × ℝ => -q.2 / 2) = fun q : ℝ × ℝ => (-(1 / 2 : ℝ)) * q.2 := by
      funext q; ring
    rw [this]
    rw [fderiv_const_mul (by fun_prop) _]
    · simp [fderiv_snd]
  rw [e₁, e₂]
  norm_num

/-- Concrete instance: for the symmetric gauge connection the Berry phase around a rectangular
loop equals the enclosed area. -/
