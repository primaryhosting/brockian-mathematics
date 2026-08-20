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

theorem mem_ker_blockOp_iff (A : U →L[𝕜] U) (C : W →L[𝕜] U) (B : U →L[𝕜] W) (D : W →L[𝕜] W)
    (z : 𝕜) (x : WithLp 2 (U × W)) :
    x ∈ LinearMap.ker ((blockOp A C B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) :
        WithLp 2 (U × W) →ₗ[𝕜] WithLp 2 (U × W)) ↔
      (A (WithLp.ofLp x).1 + C (WithLp.ofLp x).2 - z • (WithLp.ofLp x).1 = 0 ∧
        B (WithLp.ofLp x).1 + D (WithLp.ofLp x).2 - z • (WithLp.ofLp x).2 = 0) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h0 : WithLp.ofLp ((blockOp A C B D - z • 1) x) = 0 := by
      rw [show ((blockOp A C B D - z • 1 : WithLp 2 (U × W) →L[𝕜] WithLp 2 (U × W)) x) = 0 from h]
      rfl
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply] at h0
    exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
  · rintro ⟨h1, h2⟩
    refine WithLp.ofLp_injective 2 ?_
    have h3 : WithLp.ofLp (blockOp A C B D x - z • x) =
        (A (WithLp.ofLp x).1 + C (WithLp.ofLp x).2 - z • (WithLp.ofLp x).1,
          B (WithLp.ofLp x).1 + D (WithLp.ofLp x).2 - z • (WithLp.ofLp x).2) := rfl
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
    rw [h3, h1, h2]
    rfl

variable {A : U →L[𝕜] U} {C : W →L[𝕜] U} {B : U →L[𝕜] W} {D : W →L[𝕜] W} {z : 𝕜} {R : W →L[𝕜] W}

/-- **The exact Feshbach–Schur equations.** A vector `x = (a, w)` lies in the kernel of `M - z`
if and only if `w = -(D - z)⁻¹ B a` and `a` lies in the kernel of the Feshbach map. -/
