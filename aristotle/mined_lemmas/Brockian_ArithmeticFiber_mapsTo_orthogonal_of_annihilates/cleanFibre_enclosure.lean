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
# Arithmetic fibre perturbation and Feshbach–Schur transfer

This file develops, over a real or complex (`RCLike`) inner product space,
two packages of operator-theoretic results.

## Part A — gap stability

For a self-adjoint operator `L` with a protected kernel vector `u` (`L u = 0`) and a spectral
gap `g > 0` on `uᗮ`, and a self-adjoint perturbation `E` with `E u = 0` and `‖E‖ ≤ eps < g`:

* `Brockian.ArithmeticFiber.orthogonal_invariant_of_annihilates`: `uᗮ` is invariant.
* `Brockian.ArithmeticFiber.perturbation_stability`: the quadratic form of `L + E` on `uᗮ`
  is bounded below by `(g - eps) * ‖x‖ ^ 2`.
* `Brockian.ArithmeticFiber.eigenvalue_displacement`: every eigenvalue of `L + E` with
  eigenvector orthogonal to `u` is at least `g - eps`; the kernel stays protected.

## Part B — exact Feshbach–Schur reduction

For an orthogonal decomposition `H = U ⊕ W` (modelled by `WithLp 2 (U × W)`) and a block
operator `M = [[A, B*], [B, D]]` (`blockOp`, self-adjoint by `isSelfAdjoint_blockOp`), with `z`
a scalar such that `D - z` is invertible with inverse `R`, the Feshbach map is
`feshbachOp A B* B z R = A - z - B* R B`.

* `mem_ker_blockOp_iff_feshbach`: the exact Feshbach–Schur equations.
* `feshbach_schur_kernel_equiv`: `ker (M - z) ≃ₗ ker (F z)`, with explicit forward map
  `x ↦ x₁` and inverse map `a ↦ (a, -(D - z)⁻¹ B a)`.
* `norm_sub_smul_lower_bound_infDist`, `isUnit_sub_smul_of_infDist`: for self-adjoint `D` in
  finite dimension, `dist z (spectrum D) ≥ delta > 0` gives invertibility of `D - z` together
  with the resolvent bound `‖(D - z)⁻¹‖ ≤ 1 / delta`.
* `feshbach_schur_enclosure`: `‖B* (D - z)⁻¹ B‖ ≤ ‖B‖ ^ 2 / delta`.
* `spectral_enclosure_of_lower_bound`, `feshbach_schur_spectral_enclosure`,
  `spectrum_blockOp_subset`: the resulting spectral enclosure for `M`.
* `fibreResolvent`, `effectiveBaseOp`, `cleanFibre_kernel_equiv`, `cleanFibre_enclosure`,
  `cleanFibre_spectral_enclosure`: the specialization to a clean blow-up, where the fibre block
  is the identity `D = 1` on the zero-sum fibre space. There the effective base operator is
  `A - (1 - z)⁻¹ B* B` and the enclosure reads `‖B* (1 - z)⁻¹ B‖ ≤ ‖B‖ ^ 2 / ‖z - 1‖`.

All results are stated over a real or complex scalar field `𝕜` (`RCLike`).
-/

open scoped InnerProductSpace
open RCLike

namespace Brockian.ArithmeticFiber

section PartA

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A self-adjoint operator annihilating `u` maps everything into `uᗮ`; in particular the
orthogonal complement of the protected vector `u` is an invariant subspace. -/

theorem cleanFibre_enclosure (B : U →L[𝕜] W) (hz : z ≠ 1) :
    ‖(adjoint B) ∘L (fibreResolvent W z ∘L B)‖ ≤ ‖B‖ ^ 2 / ‖z - 1‖ := by
  have hne : ‖z - 1‖ ≠ 0 := by
    simpa [sub_eq_zero] using hz
  have hpos : 0 < ‖z - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hadj : ‖adjoint B‖ = ‖B‖ := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint B
  have hc1 : ‖(adjoint B) ∘L (fibreResolvent W z ∘L B)‖
      ≤ ‖adjoint B‖ * ‖fibreResolvent W z ∘L B‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have hc2 : ‖fibreResolvent W z ∘L B‖ ≤ ‖fibreResolvent W z‖ * ‖B‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hR := norm_fibreResolvent_le (W := W) hz
  rw [hadj] at hc1
  have h3 : ‖B‖ * ((1 / ‖z - 1‖) * ‖B‖) = ‖B‖ ^ 2 / ‖z - 1‖ := by field_simp
  nlinarith [norm_nonneg B, norm_nonneg (fibreResolvent W z),
    norm_nonneg (fibreResolvent W z ∘L B)]

open ContinuousLinearMap in
/-- **Part B.6 — spectral enclosure for a clean blow-up.** Away from `z = 1`, if `z` is farther
from the spectrum of the base block `A` than `‖B‖ ^ 2 / ‖z - 1‖`, then `z` is not in the spectrum
of the full operator. -/
