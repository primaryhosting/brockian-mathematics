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

lemma cycleRoot_step {m : ℕ} (j k : Fin (m + 3)) :
    cycleRoot (m + 3) ^ (((j + 1 : Fin (m + 3)) : ℕ) * (k : ℕ))
      = cycleRoot (m + 3) ^ ((j : ℕ) * (k : ℕ)) * cycleRoot (m + 3) ^ ((k : ℕ)) := by
  rw [← pow_add]
  refine cycleRoot_pow_congr (by omega) ?_
  have h1 : ((j + 1 : Fin (m + 3)) : ℕ) = ((j : ℕ) + 1) % (m + 3) := by
    rw [Fin.val_add]
    congr 1
  have h2 : ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) := by ring
  rw [h1, ← h2]
  exact (Nat.mod_modEq _ _).mul_right _

