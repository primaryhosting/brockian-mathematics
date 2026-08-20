import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Matrix

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form attached to a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

theorem qf_eq_sum {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) (x : m → 𝕜) :
    qf Q x = ∑ i, hQ.eigenvalues i *
      ‖(star (hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hQ.eigenvectorUnitary.2
  have hx : U *ᵥ (star U *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hdiag : Uᴴ * Q * U = Matrix.diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hQ.eigenvalues) := by
    have h := hQ.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hU, Matrix.star_eq_conjTranspose, mul_assoc] using h
  calc qf Q x = qf Q (U *ᵥ (star U *ᵥ x)) := by rw [hx]
    _ = qf (Uᴴ * Q * U) (star U *ᵥ x) := qf_conj _ _ _
    _ = _ := by rw [hdiag, qf_diagonal]

/-- The positive index of inertia `n₊(Q)` of a matrix: the number of positive eigenvalues of `Q`
if `Q` is Hermitian (and `0` otherwise). -/
