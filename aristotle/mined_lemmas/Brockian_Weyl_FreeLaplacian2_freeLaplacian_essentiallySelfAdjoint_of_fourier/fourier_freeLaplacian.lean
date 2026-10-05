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
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex ComplexInnerProductSpace FourierTransform

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## Essential self-adjointness -/

/-- A (densely defined) operator `T` with domain `D` inside a complex inner product space `H`
is *essentially self-adjoint* when it is densely defined, symmetric, and the ranges of
`T + i` and `T - i` are dense (the basic criterion for essential self-adjointness of a
symmetric operator). -/

lemma fourier_freeLaplacian (f : freeLaplacianDomain E) :
    ⇑(Lp.fourierTransformₗᵢ E ℂ (freeLaplacian E f))
      =ᵐ[volume] fun ξ => ((freeMultiplier E ξ : ℝ) : ℂ) *
        ⇑(Lp.fourierTransformₗᵢ E ℂ (f : Lp (α := E) ℂ 2)) ξ := by
  rw [freeLaplacian, conjOp_apply']
  exact multOp_coeFn _ _

/-- **The free Laplacian is essentially self-adjoint.**  Conjugating by the Fourier transform
turns `-Δ` into multiplication by the real symbol `4π²‖ξ‖²`, which is essentially
self-adjoint (indeed self-adjoint) on its maximal domain. -/
