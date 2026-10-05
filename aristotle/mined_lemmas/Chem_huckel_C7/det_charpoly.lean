/- (Lean requires `import` to precede any module docstring `/-! ... -/`, so this header
is given as a plain block comment.)
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex Real

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `Fin 7`
(where addition is modulo `7`): vertices `i` and `j` are adjacent iff they differ by one
step around the cycle. -/

lemma det_charpoly (μ : ℂ) :
    (C7C - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)).det = ∏ k : Fin 7, (((ev k : ℝ) : ℂ) - μ) := by
  have key : (C7C - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)) * Fm
      = Fm * (Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ))
          - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)) := by
    rw [sub_mul, mul_sub, C7C_mul_Fm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, diag_sub, Matrix.det_diagonal] at h
  exact mul_right_cancel₀ Fm_det_ne_zero (h.trans (mul_comm _ _))

