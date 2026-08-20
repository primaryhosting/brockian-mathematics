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

theorem dense_shift_range {c : ℂ} (hc : ∀ ξ : Euc d, symbol d ξ + c ≠ 0) :
    Dense ((LinearMap.range (shiftMap (freeLaplacian d) c) : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  set e : L2 d ≃ₗᵢ[ℂ] L2 d := (MeasureTheory.Lp.fourierTransformₗᵢ (Euc d) ℂ).symm with he
  have himg := dense_image_homeomorph e.toHomeomorph (dense_smooth_compactSupport d)
  refine himg.mono ?_
  rintro - ⟨-, ⟨g, hgcs, rfl⟩, rfl⟩
  obtain ⟨f, hf⟩ := exists_solution d hc g hgcs
  refine ⟨⟨toL2 d f, mem_domain_freeLaplacian d f⟩, ?_⟩
  have hval : shiftMap (freeLaplacian d) c ⟨toL2 d f, mem_domain_freeLaplacian d f⟩
      = toL2 d (negLaplacianS d f + c • f) := by
    rw [shiftMap_apply, freeLaplacian_apply, _root_.map_add, _root_.map_smul]
  rw [hval, hf]
  show toL2 d (𝓕⁻ g) = 𝓕⁻ (toL2 d g)
  exact (SchwartzMap.toLp_fourierInv_eq g).symm

/-! ## Main theorem -/

/-- **The free Laplacian is essentially self-adjoint.**  The operator `-Δ` with domain the
Schwartz space `𝓢(ℝ^d, ℂ)` inside `L²(ℝ^d, ℂ)` is essentially self-adjoint; the proof goes
through the Fourier transform, which turns `-Δ` into multiplication by `4π²‖ξ‖²`. -/
