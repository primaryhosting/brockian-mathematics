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

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity, i.e. over the index set of the matrix). -/

lemma quadForm_eq_complex (hA : A.IsHermitian) (x : Fin d → ℂ) :
    star x ⬝ᵥ A *ᵥ x = ((∑ i, hA.eigenvalues i * ‖eigCoord hA x i‖ ^ 2 : ℝ) : ℂ) := by
  have hinner : star x ⬝ᵥ A *ᵥ x
      = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin d)) (WithLp.toLp 2 (A *ᵥ x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]
  have hY : ∀ i : Fin d, inner ℂ (hA.eigenvectorBasis i)
      (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ (Fin d))
      = (hA.eigenvalues i : ℂ) * eigCoord hA x i := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, dotProduct_mulVec,
      show star (⇑(hA.eigenvectorBasis i) : Fin d → ℂ)
          ᵥ* A = star (A *ᵥ (⇑(hA.eigenvectorBasis i) : Fin d → ℂ)) by rw [star_mulVec, hA.eq],
      hA.mulVec_eigenvectorBasis]
    simp [eigCoord, star_smul, smul_dotProduct]
  have hX : ∀ i : Fin d, inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin d))
      (hA.eigenvectorBasis i) = starRingEnd ℂ (eigCoord hA x i) := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [eigCoord, star_dotProduct, dotProduct_comm]
  rw [hinner, ← (hA.eigenvectorBasis).sum_inner_mul_inner]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hX, hY]
  have h : (starRingEnd ℂ) (eigCoord hA x i) * eigCoord hA x i
      = ((‖eigCoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  linear_combination (hA.eigenvalues i : ℂ) * h

/-- Diagonalization of the Hermitian quadratic form in eigenvector coordinates (real part). -/
