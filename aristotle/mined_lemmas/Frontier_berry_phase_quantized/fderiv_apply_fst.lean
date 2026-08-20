/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory Set intervalIntegral

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` associated to a Berry connection with
components `A₁, A₂ : ℝ × ℝ → ℝ` on a two-dimensional parameter space. -/

theorem fderiv_apply_fst (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (x y : ℝ) :
    fderiv ℝ f (x, y) (1, 0) = deriv (fun t : ℝ => f (t, y)) x := by
  have hline : HasFDerivAt (fun t : ℝ => (t, y)) ((ContinuousLinearMap.id ℝ ℝ).prod 0) x := by
    exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
  have hcomp : HasDerivAt (fun t : ℝ => f (t, y)) (fderiv ℝ f (x, y) (1, 0)) x := by
    have := ((hf (x, y)).hasFDerivAt.comp x hline).hasDerivAt
    simpa using this
  exact (hcomp.deriv).symm

/-- Key intermediate lemma (second partial derivative): for a continuously differentiable
function on the plane, applying the Fréchet derivative to the second basis vector computes the
partial derivative in the second variable. -/
