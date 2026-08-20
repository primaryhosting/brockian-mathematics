/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment; its text is otherwise verbatim.)

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `Fin 8` with cyclic
successor/predecessor. -/

lemma det_sub_smul (μ : ℂ) :
    (C8adj - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)).det = ∏ k : Fin 8, ((C8eig k : ℂ) - μ) := by
  have hmul : (C8adj - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)) * P
      = P * (D - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)) := by
    rw [sub_mul, mul_sub, C8adj_mul_P, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hD : (D - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)).det = ∏ k : Fin 8, ((C8eig k : ℂ) - μ) := by
    rw [D, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.det_diagonal]
  rw [hD] at hdet
  exact mul_right_cancel₀ P_det_ne_zero (by rw [hdet]; ring)

/-- **Hückel theory for the cycle `C₈`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₈` if and only if `μ = 2 cos (2πk/8)` for some
`k ∈ {0, …, 7}`. -/
