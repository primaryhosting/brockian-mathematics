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

theorem eq_zero_of_integral_eq_zero (c : ℂ) (hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + c ≠ 0)
    (w : Lp (α := V) ℂ 2 volume)
    (hw : ∀ φ : 𝓢(V, ℂ), ∫ ξ, (starRingEnd ℂ) ((((symb ξ : ℝ) : ℂ) + c) * φ ξ) * (w ξ) = 0) :
    w = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hli : LocallyIntegrable (fun ξ => (w ξ : ℂ)) volume :=
    (Lp.memLp w).locallyIntegrable one_le_two
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
  intro g hg_smooth hg_supp
  set ψ : V → ℂ := fun ξ => (g ξ : ℂ) * ((((symb ξ : ℝ) : ℂ) + c))⁻¹ with hψ
  have hden : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : V => (((symb ξ : ℝ) : ℂ) + c)) := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : V => (symb ξ : ℝ)) :=
      contDiff_const.mul (contDiff_norm_sq ℝ)
    exact (Complex.ofRealCLM.contDiff.comp this).add contDiff_const
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    ContDiff.mul (Complex.ofRealCLM.contDiff.comp hg_smooth) (hden.inv hc)
  have hsupp : HasCompactSupport ψ :=
    HasCompactSupport.mul_right (hg_supp.comp_left (g := fun r : ℝ => (r : ℂ)) rfl)
  set φ : 𝓢(V, ℂ) := hsupp.toSchwartzMap hsmooth with hφ
  have hφapp : ∀ ξ, φ ξ = ψ ξ := fun ξ => HasCompactSupport.toSchwartzMap_toFun hsupp hsmooth ξ
  rw [← hw φ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show g ξ • (w ξ : ℂ) = (starRingEnd ℂ) ((((symb ξ : ℝ) : ℂ) + c) * φ ξ) * (w ξ)
  rw [hφapp ξ, hψ]
  simp only
  rw [← mul_assoc, mul_comm ((((symb ξ : ℝ) : ℂ) + c)) ((g ξ : ℂ)), mul_assoc,
    mul_inv_cancel₀ (hc ξ), mul_one]
  simp [Complex.real_smul]

/-- If `u ∈ L²` is orthogonal to `(-Δ + c)𝓢(V)`, then `u = 0`.  This is the Plancherel step: on
the Fourier side the operator becomes multiplication by the nowhere vanishing function
`4π²‖ξ‖² + c`. -/
