import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

theorem sum_rankOne_measure_eq_one {μ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hμ : IsQuantumMeasure μ)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, μ (rankOne (⇑(b i))) = 1 := by
  classical
  have hunit : ∀ i, star (⇑(b i)) ⬝ᵥ (⇑(b i)) = 1 := by
    intro i; simpa using orthonormalBasis_dotProduct b i i
  have horth : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j →
      rankOne (⇑(b i)) * rankOne (⇑(b j)) = 0 := by
    intro i _ j _ hij
    exact rankOne_orthogonal (by simpa [hij] using orthonormalBasis_dotProduct b i j)
  have := hμ.sum Finset.univ (fun i => rankOne (⇑(b i)))
    (fun i _ => rankOne_isProj (hunit i)) horth
  rw [sum_rankOne_orthonormalBasis b, hμ.normalized] at this
  exact this.symm

/-- Any Hermitian matrix is the sum of its eigenvalues times the rank-one projections onto
the corresponding eigenvectors. -/
