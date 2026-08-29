import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
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
set_option pp.letVarTypes true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Infinitesimal (Noether) form of a continuous symmetry.**
If `V` is differentiable and invariant under a one-parameter family of transformations
`Φ t` with `Φ 0 = id` whose velocity field at `t = 0` is `A`, then the gradient of `V`
annihilates the symmetry direction `A x` at every field configuration `x`. -/

theorem hasFDerivAt_mexHatGrad :
    HasFDerivAt mexHatGrad mexHatHessian ((1 : ℝ), (0 : ℝ)) := by
  set x₀ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with hx₀
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (fst ℝ ℝ ℝ) x₀ := (fst ℝ ℝ ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (snd ℝ ℝ ℝ) x₀ := (snd ℝ ℝ ℝ).hasFDerivAt
  have hc : HasFDerivAt (fun q : ℝ × ℝ => 2 * (q.1 ^ 2 + q.2 ^ 2 - 1))
      ((4 * x₀.1) • (fst ℝ ℝ ℝ) + (4 * x₀.2) • (snd ℝ ℝ ℝ)) x₀ := by
    have hq : HasFDerivAt (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 - 1)
        ((2 * x₀.1) • (fst ℝ ℝ ℝ) + (2 * x₀.2) • (snd ℝ ℝ ℝ)) x₀ := by
      simpa using ((h1.pow 2).add (h2.pow 2)).sub_const 1
    refine (hq.const_mul (2 : ℝ)).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp
    ring
  have hfun : (fun q : ℝ × ℝ => (2 * q.1) • (fst ℝ ℝ ℝ) + (2 * q.2) • (snd ℝ ℝ ℝ))
      = ⇑mexHatGradAux := by
    funext q
    exact ContinuousLinearMap.ext fun v => by simp [mexHatGradAux]
  have hL : HasFDerivAt (fun q : ℝ × ℝ => (2 * q.1) • (fst ℝ ℝ ℝ) + (2 * q.2) • (snd ℝ ℝ ℝ))
      mexHatGradAux x₀ := by
    rw [hfun]; exact mexHatGradAux.hasFDerivAt
  have key : HasFDerivAt mexHatGrad _ x₀ := hc.smul hL
  refine key.congr_fderiv
    (ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_)
  simp [mexHatHessian, hx₀, mexHatGradAux]
  ring

/-- The Mexican-hat potential is (infinitesimally) invariant under rotations. -/
