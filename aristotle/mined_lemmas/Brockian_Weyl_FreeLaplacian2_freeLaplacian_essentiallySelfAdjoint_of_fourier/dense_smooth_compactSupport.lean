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

theorem dense_smooth_compactSupport :
    Dense {u : L2 d | ∃ g : 𝓢(Euc d, ℂ), HasCompactSupport (g : Euc d → ℂ) ∧ u = toL2 d g} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le
    (p := 2) (by norm_num) (by norm_num) (Lp.memLp f) hε
  refine ⟨toL2 d (hg₁.toSchwartzMap hg₂), ⟨hg₁.toSchwartzMap hg₂, hg₁, rfl⟩, ?_⟩
  have hae : (f : Euc d → ℂ) - (((hg₁.toSchwartzMap hg₂).toLp 2 (volume : Measure (Euc d))
        : L2 d) : Euc d → ℂ) =ᶠ[ae (volume : Measure (Euc d))] (f : Euc d → ℂ) - g := by
    filter_upwards [(hg₁.toSchwartzMap hg₂).coeFn_toLp 2 (volume : Measure (Euc d))]
    simp
  show dist (toL2 d (hg₁.toSchwartzMap hg₂)) f ≤ ε
  rw [dist_comm]
  simp only [Lp.dist_def]
  show (eLpNorm ((f : Euc d → ℂ) - (((hg₁.toSchwartzMap hg₂).toLp 2 (volume : Measure (Euc d))
        : L2 d) : Euc d → ℂ)) 2 volume).toReal ≤ ε
  rw [eLpNorm_congr_ae hae]
  calc (eLpNorm ((f : Euc d → ℂ) - g) 2 volume).toReal ≤ (ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hg₃
    _ = ε := ENNReal.toReal_ofReal hε.le

/-- Given a smooth compactly supported `g` and `c` with `symbol d ξ + c ≠ 0` for all `ξ`, the
equation `(-Δ + c) f = 𝓕⁻¹ g` has a Schwartz solution: divide by the symbol on the Fourier
side, which preserves smoothness and compact support. -/
