import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

theorem huckel_C17_roots (z : ℂ) :
    C17adj.charpoly.IsRoot z ↔
      ∃ k : Fin 17, z = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ) := by
  rw [huckel_C17, Polynomial.IsRoot.def, Polynomial.eval_prod]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, by simpa [sub_eq_zero] using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by simp [hk]⟩

/-- Explicit eigenvectors: the `k`-th Fourier mode `j ↦ ζ^{jk}` is a nonzero eigenvector of the
adjacency matrix with eigenvalue `2 cos (2πk/17)`. -/
