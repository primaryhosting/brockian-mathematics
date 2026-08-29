/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix ComplexConjugate

namespace QI

variable {A B : Type*}

/-- `IsSchmidtDecomposition M r lam e f` says that the bipartite pure state whose amplitude
matrix is `M` (so that the state is `∑ i j, M i j • |i⟩ ⊗ |j⟩`) is written as

`M i j = ∑ k, (lam k) * e k i * f k j`

where the `lam k` are strictly positive real *Schmidt coefficients* and `e`, `f` are
orthonormal families in the two tensor factors. -/
structure IsSchmidtDecomposition [Fintype A] [Fintype B] (M : Matrix A B ℂ) (r : ℕ)
    (lam : Fin r → ℝ) (e : Fin r → A → ℂ) (f : Fin r → B → ℂ) : Prop where
  /-- Schmidt coefficients are strictly positive. -/
  coeff_pos : ∀ k, 0 < lam k
  /-- The left Schmidt vectors are orthonormal. -/
  left_orthonormal : ∀ k l, ∑ i, conj (e k i) * e l i = if k = l then 1 else 0
  /-- The right Schmidt vectors are orthonormal. -/
  right_orthonormal : ∀ k l, ∑ j, conj (f k j) * f l j = if k = l then 1 else 0
  /-- The state is the corresponding sum of product states. -/
  sum_eq : ∀ i j, M i j = ∑ k, (lam k : ℂ) * e k i * f k j

/-! ### A multiset of positive reals is determined by its power sums -/


private lemma reducedDensity_eq (h : IsSchmidtDecomposition M r lam e f) :
    M * Mᴴ = (leftMat e) * Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2)) * (leftMat e)ᴴ := by
  classical
  ext i i'
  have hR : ∀ k l : Fin r, ∑ j, f k j * conj (f l j) = if l = k then (1 : ℂ) else 0 := by
    intro k l
    rw [← h.right_orthonormal l k]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hRHS : ((leftMat e) * Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2)) * (leftMat e)ᴴ) i i'
      = ∑ k, e k i * ((lam k : ℂ) ^ 2 * conj (e k i')) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diagonal_mul]
    simp [leftMat]
  have hLHS : (M * Mᴴ) i i' = ∑ k, e k i * ((lam k : ℂ) ^ 2 * conj (e k i')) := by
    rw [Matrix.mul_apply]
    have hL : ∀ j : B, M i j * (Mᴴ) j i'
        = ∑ k, ∑ l, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
            * (f k j * conj (f l j)) := by
      intro j
      rw [Matrix.conjTranspose_apply, h.sum_eq i j, h.sum_eq i' j, RCLike.star_def, map_sum,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [map_mul, Complex.conj_ofReal]
      ring
    simp only [hL]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    have hin : ∀ l : Fin r, ∑ j, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
          * (f k j * conj (f l j))
        = ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
            * (if l = k then (1 : ℂ) else 0) := by
      intro l
      rw [← hR k l, Finset.mul_sum]
    simp only [hin]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
      ring
    · intro l _ hlk
      rw [if_neg hlk, mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ k) hc
  rw [hLHS, hRHS]

