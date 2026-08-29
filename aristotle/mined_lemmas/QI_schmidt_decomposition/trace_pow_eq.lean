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


theorem trace_pow_eq (h : IsSchmidtDecomposition M r lam e f) (p : ℕ) :
    ((M * Mᴴ) ^ (p + 1)).trace = ((∑ k, (lam k) ^ (2 * (p + 1)) : ℝ) : ℂ) := by
  rw [pow_reducedDensity h p,
    Matrix.trace_mul_comm ((leftMat e) * (Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2))) ^ (p + 1))
      ((leftMat e)ᴴ), ← Matrix.mul_assoc, leftMat_conjTranspose_mul h, Matrix.one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.pow_apply]
  rw [← pow_mul]

end Trace

/-! ### Existence -/

/-- Spectral theorem, packaged as an orthonormal eigenbasis written out in coordinates. -/
