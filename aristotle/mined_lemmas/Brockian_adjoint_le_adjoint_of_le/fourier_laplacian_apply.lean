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
# A basic criterion for essential self-adjointness

This file develops, from scratch, the classical criterion of von Neumann:

If `A` is a densely defined symmetric operator on a complex Hilbert space `H` such that the
ranges of `A + i` and `A - i` are dense — stated here in the equivalent form that a vector
orthogonal to such a range vanishes — then the adjoint `A†` is self-adjoint.  This is exactly
the statement that `A` is *essentially self-adjoint*: the closure of `A` (which is `A††`) is
self-adjoint, equivalently `A` has a unique self-adjoint extension, namely `A†`.

## Main results

* `Brockian.isSelfAdjoint_adjoint_of_denseRange`: the criterion.
* `Brockian.eq_adjoint_of_isSelfAdjoint_of_le`: uniqueness of the self-adjoint extension.
-/

open scoped ComplexInnerProductSpace
open LinearPMap

noncomputable section

namespace Brockian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Antitonicity of the adjoint: an extension has a smaller adjoint. -/

theorem fourier_laplacian_apply (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) (ξ : EuclSpace d) :
    𝓕 (Δ f) ξ = -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ (EuclSpace d) with hb
  have hsum : ∑ i, ((inner ℝ ξ (b i) : ℝ)) ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner ξ ξ]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (b i) ξ]; ring
  rw [SchwartzMap.laplacian_eq_sum b f]
  rw [show (𝓕 (∑ i, ∂_{b i} (∂_{b i} f))) = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) from
    map_sum (SchwartzMap.fourierTransformCLM ℂ) _ _]
  rw [SchwartzMap.sum_apply]
  have h1 : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = ((-((2 * Real.pi) ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2) : ℝ) : ℂ) * 𝓕 f ξ := by
    intro i
    rw [fourier_lineDerivOp_apply, fourier_lineDerivOp_apply]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp_rw [h1]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  have h2 : ∑ i, -((2 * Real.pi) ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2)
      = -((2 * Real.pi) ^ 2 * ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [h2, hsum]
  push_cast
  ring

/-! ### Density and symmetry -/

