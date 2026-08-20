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

private lemma deriv_snd_eq {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    deriv (fun y : ℝ => f (x, y)) y = fderiv ℝ f (x, y) (0, 1) := by
  have h : HasDerivAt (fun y : ℝ => f (x, y)) (fderiv ℝ f (x, y) (0, 1)) y := by
    have h₁ : HasDerivAt (fun y : ℝ => (x, y)) ((0 : ℝ), (1 : ℝ)) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    exact (hf (x, y)).hasFDerivAt.comp_hasDerivAt y h₁
  exact h.deriv

/-- **Berry phase = flux of the Berry curvature.**

For a continuously differentiable Berry connection `A` on a two–dimensional parameter space, the
Berry phase around the closed rectangular loop with corners `(a₁, a₂)` and `(b₁, b₂)` equals the
integral of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` over the enclosed region.

This is Green's theorem; it is deduced from Mathlib's divergence theorem in the plane,
`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`. -/
