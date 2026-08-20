import Mathlib

/-!
# Hückel π-energies of the cycle graph `C n`

The adjacency (Hückel) matrix of the cycle graph `C n` (`n ≥ 3`) has spectrum
`{2 cos (2 π k / n) : k = 0, …, n-1}`, and its characteristic polynomial is
`∏ k, (X - 2 cos (2 π k / n))`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

theorem huckel_cycle_charpoly {n : ℕ} (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ).charpoly
      = ∏ k : Fin n, (X - C ((huckelEnergy n k : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨u, hu⟩ := cycleDFT_isUnit m
  have hkey := adjMatrix_mul_cycleDFT m
  rw [← hu] at hkey
  have hA : (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ
      = (u : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) *
          Matrix.diagonal (fun k : Fin (m + 3) => ((huckelEnergy (m + 3) k : ℝ) : ℂ)) *
          (↑u⁻¹ : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) := by
    rw [← hkey, mul_assoc, Units.mul_inv, mul_one]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel spectrum of the cycle.** The eigenvalues of the adjacency (Hückel) matrix of the
cycle graph `C n` for `n ≥ 3` are exactly the π-energies `2 cos (2 π k / n)`,
`k = 0, …, n - 1`. -/
