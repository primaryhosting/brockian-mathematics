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
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- Note: Lean requires `import` commands to come before any module docstring `/-! ... -/`, so the
-- required header appears verbatim at the very top of the file as a block comment and is repeated
-- here, after the import, as the module docstring.

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
The free Laplacian `-Δ`, defined on the Schwartz space `𝓢(ℝ^d, ℂ)` regarded as a dense
subspace of `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

The proof follows the classical "basic criterion" of von Neumann/Weyl:

* an abstract criterion (`essentiallySelfAdjoint_of_dense_shift_ranges`): a densely defined
  symmetric operator whose deficiency ranges `Ran (T ± i)` are dense is essentially
  self-adjoint;
* the Fourier transform turns `-Δ` on Schwartz space into multiplication by
  `ξ ↦ 4π²‖ξ‖²` (`fourier_negLaplacianS`), and dividing a smooth compactly supported
  function by `4π²‖ξ‖² ± i` (which never vanishes) produces again a smooth compactly
  supported function.  Since smooth compactly supported functions are dense in `L²` and
  the Fourier transform is unitary on `L²` (Plancherel), the deficiency ranges are dense.
-/

open MeasureTheory SchwartzMap Filter LinearPMap
open scoped FourierTransform ComplexInnerProductSpace LinearPMap Laplacian LineDeriv Topology
  ContDiff

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The operator `T + c` on the domain of the partially defined operator `T`. -/

theorem exists_solution {c : ℂ} (hc : ∀ ξ : Euc d, symbol d ξ + c ≠ 0) (g : 𝓢(Euc d, ℂ))
    (hg : HasCompactSupport (g : Euc d → ℂ)) :
    ∃ f : 𝓢(Euc d, ℂ), negLaplacianS d f + c • f = 𝓕⁻ g := by
  set φfun : Euc d → ℂ := fun ξ => (symbol d ξ + c)⁻¹ * g ξ with hφfun
  have hcs : HasCompactSupport φfun := HasCompactSupport.mul_left hg
  have hcd : ContDiff ℝ ∞ φfun :=
    (((symbol_contDiff d).add contDiff_const).inv hc).mul g.smooth'
  set φ : 𝓢(Euc d, ℂ) := hcs.toSchwartzMap hcd with hφ
  refine ⟨𝓕⁻ φ, ?_⟩
  have hFφ : 𝓕 (𝓕⁻ φ) = φ := FourierTransform.fourier_fourierInv_eq φ
  apply fourier_injective
  rw [FourierTransform.fourier_fourierInv_eq g]
  have hlin : 𝓕 (negLaplacianS d (𝓕⁻ φ) + c • (𝓕⁻ φ))
      = 𝓕 (negLaplacianS d (𝓕⁻ φ)) + c • 𝓕 (𝓕⁻ φ) := by simp
  rw [hlin, hFφ]
  ext ξ
  rw [SchwartzMap.add_apply, fourier_negLaplacianS, hFφ, SchwartzMap.smul_apply]
  have hφval : φ ξ = (symbol d ξ + c)⁻¹ * g ξ := rfl
  rw [hφval]
  simp only [smul_eq_mul]
  have hstep : symbol d ξ * ((symbol d ξ + c)⁻¹ * g ξ) + c * ((symbol d ξ + c)⁻¹ * g ξ)
      = ((symbol d ξ + c) * (symbol d ξ + c)⁻¹) * g ξ := by ring
  rw [hstep, mul_inv_cancel₀ (hc ξ), one_mul]

