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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap ComplexInnerProductSpace FourierTransform Laplacian Real

namespace Brockian.FreeLaplacianPlancherel

noncomputable section

/-! ## An abstract criterion for essential self-adjointness

We work with a symmetric, densely defined operator `T` with domain a submodule `D` of a complex
Hilbert space `H`.  Mathlib does not (yet) have a theory of unbounded operators, so we spell out
the relevant notions.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `IsAdjointPair D T y z` says that `y` belongs to the domain of the adjoint of the operator
`T` (with domain `D`) and that `z` is a corresponding adjoint value, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain.  If `D` is dense then `z` is uniquely determined
by `y`, and `z = T* y`. -/

theorem fourier_shift_apply (c : ℂ) (f : 𝓢(V, ℂ)) (ξ : V) :
    (𝓕 ((-Δ f) + c • f)) ξ = (((symb ξ : ℝ) : ℂ) + c) * (𝓕 f) ξ := by
  have h : (𝓕 ((-Δ f) + c • f) : 𝓢(V, ℂ)) = -(𝓕 (Δ f)) + c • (𝓕 f) := by
    rw [← SchwartzMap.fourierTransformCLM_apply ℂ, map_add, map_neg, map_smul]
    simp
  rw [h]
  simp only [SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    fourier_laplacian_apply, smul_eq_mul]
  ring

/-! ### Inner products of Schwartz functions in `L²` -/

