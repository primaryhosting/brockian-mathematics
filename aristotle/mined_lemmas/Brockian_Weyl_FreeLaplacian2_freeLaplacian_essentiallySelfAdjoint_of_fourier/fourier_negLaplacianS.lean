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

theorem fourier_negLaplacianS (f : 𝓢(Euc d, ℂ)) (ξ : Euc d) :
    (𝓕 (negLaplacianS d f)) ξ = symbol d ξ * (𝓕 f) ξ := by
  set b := stdOrthonormalBasis ℝ (Euc d) with hb
  have hlap : Δ f = ∑ i, ∂_{b i} (∂_{b i} f) := SchwartzMap.laplacian_eq_sum b f
  have hneg : 𝓕 (negLaplacianS d f) = -(𝓕 (Δ f : 𝓢(Euc d, ℂ))) := by
    rw [negLaplacianS_eq]
    exact map_neg (SchwartzMap.fourierTransformCLM ℂ) _
  have hsum : 𝓕 (Δ f : 𝓢(Euc d, ℂ)) = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) := by
    rw [hlap]
    exact map_sum (SchwartzMap.fourierTransformCLM ℂ) _ _
  rw [hneg]
  simp only [SchwartzMap.neg_apply, hsum, SchwartzMap.sum_apply]
  have hterm : ∀ i, (𝓕 (∂_{b i} (∂_{b i} f))) ξ
      = -((2 * (Real.pi : ℂ)) ^ 2 * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2) * (𝓕 f) ξ := by
    intro i
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
    ring_nf
    simp [Complex.I_sq]
  simp only [hterm]
  rw [← Finset.sum_mul]
  have hnorm : ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    have hbb := b.sum_inner_mul_inner (𝕜 := ℝ) ξ ξ
    have h2 : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← hbb]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (b i) ξ]
      ring
    rw [← h2]
    push_cast
    ring
  have hs : (∑ i, -((2 * (Real.pi : ℂ)) ^ 2 * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2))
      = -((2 * (Real.pi : ℂ)) ^ 2 * ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← hnorm, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hs, symbol]
  push_cast
  ring

