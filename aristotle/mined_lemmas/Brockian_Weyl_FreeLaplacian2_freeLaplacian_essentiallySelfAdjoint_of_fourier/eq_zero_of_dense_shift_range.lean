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

theorem eq_zero_of_dense_shift_range {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E)) {c : ℂ}
    (hd : Dense ((LinearMap.range (shiftMap T c) : Submodule ℂ E) : Set E))
    (y : T†.domain) (hy : T† y = -(starRingEnd ℂ c) • (y : E)) : (y : E) = 0 := by
  refine hd.eq_zero_of_inner_left ?_
  rintro ⟨-, ⟨x, rfl⟩⟩
  have hfa : T†.IsFormalAdjoint T := LinearPMap.adjoint_isFormalAdjoint hT
  have h1 : ⟪T† y, (x : E)⟫ = ⟪(y : E), T x⟫ := hfa y x
  simp only [shiftMap_apply, inner_add_right, inner_smul_right]
  rw [← h1, hy]
  simp [inner_smul_left]

