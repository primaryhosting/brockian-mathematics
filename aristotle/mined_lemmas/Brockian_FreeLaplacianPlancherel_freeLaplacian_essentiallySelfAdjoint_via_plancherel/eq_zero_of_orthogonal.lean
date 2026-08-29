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

theorem eq_zero_of_orthogonal (c : ℂ) (hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + c ≠ 0)
    (u : Lp (α := V) ℂ 2 volume)
    (h0 : ∀ f : 𝓢(V, ℂ), ⟪((-Δ f) + c • f).toLp 2 volume, u⟫ = 0) : u = 0 := by
  have hw : ∀ φ : 𝓢(V, ℂ),
      ∫ ξ, (starRingEnd ℂ) ((((symb ξ : ℝ) : ℂ) + c) * φ ξ) *
        ((𝓕 u : Lp (α := V) ℂ 2 volume) ξ) = 0 := by
    intro φ
    obtain ⟨f, hf⟩ : ∃ f : 𝓢(V, ℂ), 𝓕 f = φ := ⟨𝓕⁻ φ, FourierTransform.fourier_fourierInv_eq φ⟩
    have h1 : ⟪𝓕 (((-Δ f) + c • f).toLp 2 volume), 𝓕 u⟫ = 0 := by
      rw [Lp.inner_fourier_eq]; exact h0 f
    rw [SchwartzMap.toLp_fourier_eq, inner_toLp] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [fourier_shift_apply c f ξ, hf]
  have hfu : (𝓕 u : Lp (α := V) ℂ 2 volume) = 0 := eq_zero_of_integral_eq_zero c hc _ hw
  have : ‖u‖ = 0 := by
    rw [← Lp.norm_fourier_eq u, hfu, norm_zero]
  exact norm_eq_zero.mp this

/-- Density of the range of `-Δ + c` on Schwartz functions, for `c` with `4π²‖ξ‖² + c ≠ 0`. -/
