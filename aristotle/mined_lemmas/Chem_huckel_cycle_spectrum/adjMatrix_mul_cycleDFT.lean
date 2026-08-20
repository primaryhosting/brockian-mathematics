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

lemma adjMatrix_mul_cycleDFT (m : ℕ) :
    (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ * cycleDFT (m + 3)
      = cycleDFT (m + 3) *
        Matrix.diagonal (fun k : Fin (m + 3) => ((huckelEnergy (m + 3) k : ℝ) : ℂ)) := by
  ext i k
  have hstep : ∀ j : Fin (m + 3),
      cycleDFT (m + 3) (j + 1) k = cycleDFT (m + 3) j k * cycleRoot (m + 3) ^ ((k : ℕ)) := by
    intro j
    rw [cycleDFT_apply, cycleDFT_apply]
    exact cycleRoot_step j k
  have hLHS : ((SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ * cycleDFT (m + 3)) i k
      = ((SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ *ᵥ (fun j => cycleDFT (m + 3) j k)) i := rfl
  rw [hLHS, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one i), Matrix.mul_diagonal,
    huckelEnergy_eq (n := m + 3) (by omega), hstep i]
  have h1 : cycleDFT (m + 3) i k
      = cycleDFT (m + 3) (i - 1) k * cycleRoot (m + 3) ^ ((k : ℕ)) := by
    have h := hstep (i - 1)
    rwa [sub_add_cancel] at h
  have hz : cycleRoot (m + 3) ^ ((k : ℕ)) ≠ 0 := pow_ne_zero _ (cycleRoot_ne_zero _)
  rw [h1]
  field_simp
  ring

