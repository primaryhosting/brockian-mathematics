import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/

lemma qform_eq {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform M x = ∑ i, hM.eigenvalues i * ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 := by
  have hx : x = ∑ i, inner ℂ (hM.eigenvectorBasis i) x • hM.eigenvectorBasis i :=
    (hM.eigenvectorBasis.sum_repr' x).symm
  have key : Matrix.toEuclideanLin M x
      = ∑ i, ((hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x)
          • hM.eigenvectorBasis i := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, toEuclideanLin_eigenvectorBasis hM, smul_smul, mul_comm]
  rw [qform, key, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm x, mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow]
  show (((hM.eigenvalues i : ℝ) : ℂ) * ((‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ)).re = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

