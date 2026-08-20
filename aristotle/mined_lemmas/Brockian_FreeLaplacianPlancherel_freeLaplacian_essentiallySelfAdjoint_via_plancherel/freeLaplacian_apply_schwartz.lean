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

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/

theorem freeLaplacian_apply_schwartz (f : 𝓢(E, ℂ)) :
    freeLaplacian E ⟨f.toLp 2 volume, schwartz_mem_freeLaplacianDomain E f⟩
      = (-(Δ f)).toLp 2 volume := by
  have hF : (Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume) : Lp (α := E) ℂ 2 volume)
      = (𝓕 f).toLp 2 volume := SchwartzMap.toLp_fourier_eq f
  have h1 : mulOp (laplacianSymbol E) (measurable_laplacianSymbol E) volume
      ⟨Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume),
        (schwartz_mem_freeLaplacianDomain E f)⟩
      = (𝓕 (-(Δ f))).toLp 2 volume := by
    apply Subtype.ext
    show mulSymbol (laplacianSymbol E) (measurable_laplacianSymbol E) volume *
        ((Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume) : Lp (α := E) ℂ 2 volume) :
          E →ₘ[volume] ℂ) = _
    rw [hF, mulSymbol_mul_fourier_toLp]
  have h2 : ((𝓕 (-(Δ f))).toLp 2 volume : Lp (α := E) ℂ 2 volume)
      = Lp.fourierTransformₗᵢ E ℂ ((-(Δ f)).toLp 2 volume) :=
    (SchwartzMap.toLp_fourier_eq (-(Δ f))).symm
  show (Lp.fourierTransformₗᵢ E ℂ).symm (mulOp (laplacianSymbol E)
    (measurable_laplacianSymbol E) volume ⟨Lp.fourierTransformₗᵢ E ℂ (f.toLp 2 volume), _⟩) = _
  rw [h1, h2, LinearIsometryEquiv.symm_apply_apply]

end FreeLaplacian

end Brockian.FreeLaplacianPlancherel

