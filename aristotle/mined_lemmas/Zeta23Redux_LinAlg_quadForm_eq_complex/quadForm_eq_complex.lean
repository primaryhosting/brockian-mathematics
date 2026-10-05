import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
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

namespace Zeta23Redux.LinAlg

open Matrix

/-- The coordinates of a vector `x` in the eigenbasis of a Hermitian matrix `A`, i.e.
`x` expressed via the unitary matrix of eigenvectors of `A`. -/

theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℂ) ^ 2) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set y : n → ℂ := eigencoord hA x with hy
  have hyx : y = star U *ᵥ x := rfl
  have hstar : star y = star x ᵥ* U := by
    rw [hyx, Matrix.star_mulVec]
    simp [hU, Matrix.star_eq_conjTranspose]
  calc star x ⬝ᵥ A *ᵥ x
      = star x ⬝ᵥ (U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U) *ᵥ x := by
        rw [← spectral_decomp hA]
    _ = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *ᵥ y := by
        rw [hstar, hyx, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_assoc]
    _ = ∑ i, (hA.eigenvalues i : ℂ) * ((‖y i‖ : ℂ) ^ 2) := by
        rw [dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_diagonal]
        have hz : (starRingEnd ℂ) (y i) * y i = ((‖y i‖ : ℂ)) ^ 2 := by
          rw [mul_comm, Complex.mul_conj]
          norm_cast
          exact Complex.normSq_eq_norm_sq (y i)
        simp only [Pi.star_apply, Function.comp_apply]
        rw [show star (y i) = (starRingEnd ℂ) (y i) from rfl, ← mul_assoc,
          mul_comm _ ((RCLike.ofReal (hA.eigenvalues i) : ℂ)), mul_assoc, hz]
        norm_num

end Zeta23Redux.LinAlg

