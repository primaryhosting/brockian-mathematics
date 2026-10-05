/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma det_sub_smul (lam : ℂ) :
    (C10 - lam • (1 : Matrix (Fin 10) (Fin 10) ℂ)).det * F.det
      = F.det * ∏ k : Fin 10, (mu k - lam) := by
  have hmul : (C10 - lam • (1 : Matrix (Fin 10) (Fin 10) ℂ)) * F
      = F * Matrix.diagonal fun k => mu k - lam := by
    have hd : (Matrix.diagonal fun k => mu k - lam)
        = Matrix.diagonal mu - lam • (1 : Matrix (Fin 10) (Fin 10) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [hd, sub_mul, mul_sub, C10_mul_F, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have := congrArg Matrix.det hmul
  rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at this

/-- The explicit Hückel eigenvector for index `k`: the vertex `i` gets amplitude `ζ^(k i)`,
with eigenvalue `2 cos (2πk/10)`. -/
