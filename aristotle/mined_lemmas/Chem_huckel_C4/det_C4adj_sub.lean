import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene,
with `α = 0`, `β = 1`): vertices are `Fin 4` arranged in a cycle, and `i ~ j` iff
`j = i + 1` or `i = j + 1` (addition modulo `4`). -/

theorem det_C4adj_sub (μ : ℝ) :
    (C4adj - μ • (1 : Matrix (Fin 4) (Fin 4) ℝ)).det = μ ^ 4 - 4 * μ ^ 2 := by
  have h : (C4adj - μ • (1 : Matrix (Fin 4) (Fin 4) ℝ))
      = !![-μ, 1, 0, 1; 1, -μ, 1, 0; 0, 1, -μ, 1; 1, 0, 1, -μ] := by
    rw [C4adj_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Fin.castSucc, Fin.castAdd,
    Fin.castLE, Fin.succ]
  ring

/-- `μ` is an eigenvalue of `C4adj` iff the characteristic determinant vanishes. -/
