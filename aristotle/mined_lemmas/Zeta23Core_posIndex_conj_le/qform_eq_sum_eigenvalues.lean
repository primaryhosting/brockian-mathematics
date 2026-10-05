/-
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`
(for Hermitian `Q` the value `xᴴ Q x` is real, and `qform` records its real part). -/

theorem qform_eq_sum_eigenvalues (hQ : Q.IsHermitian) (x : m → 𝕜) :
    qform Q x = ∑ i, hQ.eigenvalues i *
      ‖((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x) i‖ ^ 2 := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  have hUs : Uᴴ * U = 1 := by
    simpa [hU, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hQ.eigenvectorUnitary
  have hsU : U * Uᴴ = 1 := by
    simpa [hU, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hQ.eigenvectorUnitary
  have hx : U *ᵥ (Uᴴ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hsU, Matrix.one_mulVec]
  calc qform Q x = qform Q (U *ᵥ (Uᴴ *ᵥ x)) := by rw [hx]
    _ = qform (Uᴴ * Q * U) (Uᴴ *ᵥ x) := (qform_compress Q U _).symm
    _ = qform (diagonal (RCLike.ofReal ∘ hQ.eigenvalues) : Matrix m m 𝕜) (Uᴴ *ᵥ x) := by
        rw [conjTranspose_mul_mul_eigenvectorUnitary hQ]
    _ = _ := qform_diagonal _ _

end Spectral

/-- If a linear map out of `m → 𝕜` is injective on a submodule `S`, then the dimension of `S`
is at most the dimension of the target. -/
