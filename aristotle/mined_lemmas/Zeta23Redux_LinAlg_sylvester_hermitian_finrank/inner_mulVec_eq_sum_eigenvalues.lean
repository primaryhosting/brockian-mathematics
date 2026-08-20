import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix WithLp Finset

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux.LinAlg

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The *positive index* of a Hermitian matrix `A`: the number of strictly positive
eigenvalues of `A` (counted with multiplicity, i.e. the number of indices `i` with
`hA.eigenvalues i > 0`).  It depends on `A` only, but is phrased in terms of the
hermiticity witness `hA` since Mathlib's `Matrix.IsHermitian.eigenvalues` is. -/

theorem inner_mulVec_eq_sum_eigenvalues (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ (Fin d)) :
    inner ℂ v (toLp 2 (A *ᵥ v.ofLp)) =
      ∑ i, (hA.eigenvalues i : ℂ) * ‖inner ℂ (hA.eigenvectorBasis i) v‖ ^ 2 := by
  have hv : ∑ i, ((hA.eigenvectorBasis).repr v).ofLp i • hA.eigenvectorBasis i = v :=
    hA.eigenvectorBasis.sum_repr v
  have hL : toLp 2 (A *ᵥ v.ofLp)
      = ∑ i, ((hA.eigenvectorBasis).repr v).ofLp i •
        ((hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i) := by
    rw [← Matrix.toLpLin_apply 2 2 A v]
    conv_lhs => rw [← hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Matrix.toLpLin_apply, hA.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [WithLp.toLp_smul, WithLp.toLp_ofLp]
    rfl
  rw [hL, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_right, hA.eigenvectorBasis.repr_apply_apply,
    ← Complex.mul_conj', ← inner_conj_symm (hA.eigenvectorBasis i) v, Complex.conj_conj]
  ring

/-- The Hermitian form written through the plain `dotProduct` notation. -/
