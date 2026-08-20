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

lemma det_smul_one_sub_adjC3 (μ : ℝ) :
    (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - adjC3).det = (μ - 2) * (μ + 1) ^ 2 := by
  have h : (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - adjC3) =
      !![μ, -1, -1; -1, μ, -1; -1, -1, μ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjC3]
  rw [h, Matrix.det_fin_three]
  simp
  ring

/-- The three values `2 cos (2πk/3)`, `k = 0, 1, 2`, are exactly `2`, `-1`, `-1`. -/
