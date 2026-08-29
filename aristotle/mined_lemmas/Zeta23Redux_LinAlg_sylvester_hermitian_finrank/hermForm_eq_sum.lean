import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

/-- The Hermitian form attached to a matrix `A`: `x ↦ Re (star x ⬝ᵥ (A *ᵥ x))`. -/

lemma hermForm_eq_sum (x : Fin d → ℂ) :
    hermForm A x = ∑ i, hA.eigenvalues i * Complex.normSq (diagCoord hA x i) := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  have hAeq : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, mul_assoc] using this
  have hmul : A *ᵥ x = U *ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (star U *ᵥ x)) := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M *ᵥ x) hAeq
    simpa only [← Matrix.mulVec_mulVec] using h
  have hstar : star x ᵥ* U = star (star U *ᵥ x) := by
    have : star ((Uᴴ) *ᵥ x) = star x ᵥ* (Uᴴ)ᴴ := Matrix.star_mulVec _ _
    simpa using this.symm
  have key : star x ⬝ᵥ (A *ᵥ x)
      = star (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (star U *ᵥ x)) := by
    rw [hmul, Matrix.dotProduct_mulVec, hstar]
  have : star x ⬝ᵥ (A *ᵥ x)
      = ∑ i, ((hA.eigenvalues i : ℂ) * (Complex.normSq (diagCoord hA x i) : ℂ)) := by
    rw [key]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def,
      Function.comp_apply, diagCoord, hU]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [hermForm, this]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

/-- The linear map sending a vector to its eigen-coordinates in the positive eigenspaces. -/
