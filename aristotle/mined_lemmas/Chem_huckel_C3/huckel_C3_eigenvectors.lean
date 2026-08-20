/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
with `α = 0`, `β = 1`). -/

theorem huckel_C3_eigenvectors :
    adjC3.mulVec ![1, 1, 1] = (2 : ℝ) • ![1, 1, 1] ∧
    adjC3.mulVec ![1, -1, 0] = (-1 : ℝ) • ![1, -1, 0] ∧
    adjC3.mulVec ![0, 1, -1] = (-1 : ℝ) • ![0, 1, -1] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext i
      fin_cases i <;>
        simp [adjC3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- Spectrum form of the Hückel result for `C₃`: the spectrum of the adjacency matrix is
exactly the set of Hückel eigenvalues `2 cos (2πk/3)`, `k = 0, 1, 2`. -/
