import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QI

open Matrix Polynomial Finset
open scoped ComplexConjugate ComplexOrder

variable {m n : ℕ}

/-- The elementary tensor `a ⊗ b` of `a ∈ ℂ^m` and `b ∈ ℂ^n`, viewed inside
`ℂ^m ⊗ ℂ^n ≅ ℂ^(m × n)`. -/

lemma charpoly_rho {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) :
    (rho psi).charpoly = X ^ (m - r) * ∏ k : Fin r, (X - C ((lam k : ℂ) ^ 2)) := by
  classical
  have hr := schmidt_rank_le h
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extend e h.left_orthonormal hr
  set U : Matrix (Fin m) (Fin m) ℂ := Matrix.of (fun i j => b j i) with hU
  set d : Fin m → ℂ := fun j => if hj : (j : ℕ) < r then ((lam ⟨j, hj⟩ : ℝ) : ℂ) ^ 2 else 0
    with hd
  have hdcast : ∀ k : Fin r, d (Fin.castLE hr k) = ((lam k : ℂ)) ^ 2 := by
    intro k
    simp only [hd]
    rw [dif_pos (show ((Fin.castLE hr k : Fin m) : ℕ) < r by simp [k.isLt])]
    simp
  have hdinr : ∀ l : Fin (m - r), d (finSplit hr (Sum.inr l)) = 0 := by
    intro l
    simp only [hd]
    rw [dif_neg]
    simp [finSplit_inr_val]
  have hUU : Uᴴ * U = 1 := by
    ext j j'
    rw [Matrix.mul_apply]
    simp only [hU, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
      Matrix.one_apply]
    exact (orthonormal_iff_sum (⇑b)).1 b.orthonormal j j'
  have hrho : rho psi = U * Matrix.diagonal d * Uᴴ := by
    rw [rho_eq_sum h]
    ext i i'
    simp only [Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def, hU,
      Matrix.of_apply]
    rw [sum_finSplit hr (fun j => b j i * d j * conj (b j i'))]
    simp only [hdcast, hdinr, hb, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrho, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hUU, Matrix.mul_one,
    Matrix.charpoly_diagonal, prod_finSplit hr (fun j => X - C (d j))]
  simp only [hdcast, hdinr, map_zero, sub_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

