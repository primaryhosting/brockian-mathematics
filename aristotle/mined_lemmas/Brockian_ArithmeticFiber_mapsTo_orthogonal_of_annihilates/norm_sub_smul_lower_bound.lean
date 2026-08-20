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

theorem norm_sub_smul_lower_bound [FiniteDimensional 𝕜 X] [CompleteSpace X] {D : X →L[𝕜] X}
    (hD : IsSelfAdjoint D) {z : 𝕜} {delta : ℝ}
    (hdelta : ∀ mu ∈ spectrum 𝕜 D, delta ≤ ‖mu - z‖) (w : X) :
    delta * ‖w‖ ≤ ‖(D - z • 1) w‖ := by
  rcases le_or_gt delta 0 with hd | hd
  · nlinarith [norm_nonneg w, norm_nonneg ((D - z • (1 : X →L[𝕜] X)) w)]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hD
  set n := Module.finrank 𝕜 X with hn
  set b := hsym.eigenvectorBasis (n := n) rfl with hb
  set lam := hsym.eigenvalues (n := n) rfl with hlam
  have hspec : ∀ i, ((lam i : ℝ) : 𝕜) ∈ spectrum 𝕜 D := by
    intro i
    refine mem_spectrum_of_eigen (v := b i) ?_ ?_
    · intro h0
      have h1 := b.orthonormal.1 i
      rw [h0] at h1; simp at h1
    · exact hsym.apply_eigenvectorBasis rfl i
  have key : ∀ i, ⟪b i, (D - z • (1 : X →L[𝕜] X)) w⟫_𝕜
      = (((lam i : ℝ) : 𝕜) - z) * ⟪b i, w⟫_𝕜 := by
    intro i
    have h1 : ⟪b i, D w⟫_𝕜 = ((lam i : ℝ) : 𝕜) * ⟪b i, w⟫_𝕜 := by
      have h0 : ⟪(D : X →ₗ[𝕜] X) (b i), w⟫_𝕜 = ⟪b i, (D : X →ₗ[𝕜] X) w⟫_𝕜 := hsym (b i) w
      rw [hsym.apply_eigenvectorBasis rfl i, inner_smul_left] at h0
      simpa using h0.symm
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right, h1]
    ring
  have hsum : ‖(D - z • (1 : X →L[𝕜] X)) w‖ ^ 2
      = ∑ i, ‖(((lam i : ℝ) : 𝕜) - z) * ⟪b i, w⟫_𝕜‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right]
    exact Finset.sum_congr rfl fun i _ => by rw [key i]
  have hlow : delta ^ 2 * ‖w‖ ^ 2 ≤ ‖(D - z • (1 : X →L[𝕜] X)) w‖ ^ 2 := by
    rw [hsum, ← b.sum_sq_norm_inner_right w, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_pow]
    have h1 := hdelta _ (hspec i)
    have h2 : delta ^ 2 ≤ ‖((lam i : ℝ) : 𝕜) - z‖ ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖⟪b i, w⟫_𝕜‖, norm_nonneg ⟪b i, w⟫_𝕜]
  nlinarith [norm_nonneg w, norm_nonneg ((D - z • (1 : X →L[𝕜] X)) w), hd.le]

/-- The same bound, phrased with the distance from `z` to the spectrum of `D`. -/
