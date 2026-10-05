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


private lemma pow_reducedDensity (h : IsSchmidtDecomposition M r lam e f) (p : ℕ) :
    (M * Mᴴ) ^ (p + 1)
      = (leftMat e) * (Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2))) ^ (p + 1) * (leftMat e)ᴴ := by
  induction p with
  | zero => simpa using reducedDensity_eq h
  | succ n ih =>
      rw [pow_succ, ih, reducedDensity_eq h]
      rw [pow_succ (Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2))) (n + 1)]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((leftMat e)ᴴ) (leftMat e), leftMat_conjTranspose_mul h,
        Matrix.one_mul]

/-- The trace of the `(p+1)`-st power of the reduced density matrix `M Mᴴ` is the
`(p+1)`-st power sum of the squared Schmidt coefficients. -/
