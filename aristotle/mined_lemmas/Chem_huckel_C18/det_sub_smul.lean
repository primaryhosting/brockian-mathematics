/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the annulene `C₁₈` uses the adjacency matrix of the cycle
graph `C₁₈`.  We show that its eigenvalues are exactly the `18` numbers
`2 cos (2πk/18)`, `k = 0, …, 17`.
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈` on the vertex set `Fin 18`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `18`. -/

lemma det_sub_smul (μ : ℂ) :
    (C18adj - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)).det = ∏ k : Fin 18, (lam k - μ) := by
  have hcomm : (C18adj - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)) * V
      = V * (Matrix.diagonal lam - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)) := by
    rw [sub_mul, mul_sub, C18adj_mul_V, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hdet := congrArg Matrix.det hcomm
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h2 : (Matrix.diagonal lam - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ))
      = Matrix.diagonal fun k => lam k - μ := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [h2, Matrix.det_diagonal] at hdet
  refine mul_right_cancel₀ V_det_ne_zero ?_
  rw [hdet, mul_comm]

/-- **Hückel spectrum of `C₁₈`.** A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₁₈` if and only if `μ = 2 cos (2πk/18)` for some `k < 18`. -/
