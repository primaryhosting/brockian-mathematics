import Mathlib
/-!
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The Berry connection of a family of quantum states `ψ : ℝ × ℝ → H` over a two–dimensional
parameter space, given in components by `A_j (R) = Im ⟪ψ R, ∂_j ψ R⟫`. -/

private lemma deriv_fst_eq {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    deriv (fun x : ℝ => f (x, y)) x = fderiv ℝ f (x, y) (1, 0) := by
  have h : HasDerivAt (fun x : ℝ => f (x, y)) (fderiv ℝ f (x, y) (1, 0)) x := by
    have h₁ : HasDerivAt (fun x : ℝ => (x, y)) ((1 : ℝ), (0 : ℝ)) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    exact (hf (x, y)).hasFDerivAt.comp_hasDerivAt x h₁
  exact h.deriv

/-- A partial derivative in the second variable, expressed through the total derivative. -/
