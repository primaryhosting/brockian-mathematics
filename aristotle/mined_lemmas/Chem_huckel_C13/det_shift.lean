import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
(The `import Mathlib` line must precede the module docstring: Lean 4 requires all
`import` commands to appear at the very beginning of a file.)
-/

namespace Chem

open Matrix SimpleGraph Finset

/-- A primitive 13-th root of unity. -/

lemma det_shift (mu : ℂ) :
    (Matrix.diagonal (fun _ : Fin 13 => mu) - A).det = ∏ k, (mu - lam k) := by
  have hc : ∀ M : Matrix (Fin 13) (Fin 13) ℂ,
      Matrix.diagonal (fun _ : Fin 13 => mu) * M = M * Matrix.diagonal (fun _ : Fin 13 => mu) := by
    intro M
    rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have key : (Matrix.diagonal (fun _ : Fin 13 => mu) - A) * F
      = F * Matrix.diagonal (fun k => mu - lam k) := by
    rw [sub_mul, A_mul_F, hc F, ← Matrix.diagonal_sub, Matrix.mul_sub]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ F_det_ne_zero (by linear_combination hdet :
    (Matrix.diagonal (fun _ : Fin 13 => mu) - A).det * F.det = (∏ k, (mu - lam k)) * F.det)
  exact this

/-- **Hückel theory for the cyclic polyene C₁₃H₁₃ (the cyclotridecatrienyl system).**
The eigenvalues of the adjacency matrix of the cycle graph `C₁₃` (i.e. the Hückel
matrix in units where `α = 0`, `β = 1`) are exactly the numbers
`2 cos (2πk/13)` for `k = 0, 1, …, 12`. -/
