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


private lemma exists_orthonormal_eigenbasis [Fintype A] [DecidableEq A] {R : Matrix A A ℂ}
    (hR : R.IsHermitian) :
    ∃ (mu : A → ℝ) (u : A → A → ℂ),
      (∀ k l, ∑ i, conj (u k i) * u l i = if k = l then (1 : ℂ) else 0) ∧
      (∀ i i', ∑ k, u k i * conj (u k i') = if i = i' then (1 : ℂ) else 0) ∧
      (∀ k, R *ᵥ (u k) = (mu k : ℂ) • (u k)) := by
  classical
  refine ⟨hR.eigenvalues, fun k i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k, ?_, ?_, ?_⟩
  · intro k l
    have hs := (hR.eigenvectorUnitary.2 : (hR.eigenvectorUnitary : Matrix A A ℂ) ∈ unitary _).1
    have := congrFun (congrFun hs k) l
    simpa [Matrix.mul_apply, Matrix.one_apply, RCLike.star_def] using this
  · intro i i'
    have hs := (hR.eigenvectorUnitary.2 : (hR.eigenvectorUnitary : Matrix A A ℂ) ∈ unitary _).2
    have := congrFun (congrFun hs i) i'
    simpa [Matrix.mul_apply, Matrix.one_apply, RCLike.star_def] using this
  · intro k
    have h1 := hR.mulVec_eigenvectorBasis k
    show R *ᵥ (fun i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k)
        = ((hR.eigenvalues k : ℝ) : ℂ) • (fun i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k)
    have h2 : (fun i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k)
        = (hR.eigenvectorBasis k).ofLp := rfl
    rw [h2, h1]
    funext i
    simp [Complex.real_smul]

