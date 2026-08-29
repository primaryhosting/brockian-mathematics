/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

theorem C20adj_eigenvalue_eq {mu : ℂ} (v : ZMod 20 → ℂ) (hv : v ≠ 0)
    (h : C20adj *ᵥ v = mu • v) : ∃ k : ZMod 20, mu = ((C20eigenvalue k : ℝ) : ℂ) := by
  have hdet : (Matrix.scalar (ZMod 20) mu - C20adj).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, h]
    funext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have heval := Matrix.eval_charpoly C20adj mu
  rw [hdet, C20adj_charpoly, Polynomial.eval_prod] at heval
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp heval
  refine ⟨k, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk
  exact hk

/-- **Hückel theory for the annulene C₂₀.**  The adjacency (Hückel) matrix of the cycle
graph `C₂₀` has eigenvalues exactly `2 cos (2πk/20)` for `k = 0, …, 19`:

* each `2 cos (2πk/20)` is an eigenvalue, with explicit nonzero eigenvector `C20vec k`;
* the characteristic polynomial is `∏ₖ (X - 2 cos (2πk/20))`, so there are no others,
  even counting multiplicities;
* consequently every eigenvalue is of this form. -/
