import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma qc_add_qc_inv (k : Fin 13) :
    qc k + (qc k)⁻¹ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) : ℝ) : ℂ) := by
  have h1 : (qc k)⁻¹ = Complex.exp (-(((2 * Real.pi * (k : ℕ) / 13 : ℝ) : ℂ) * Complex.I)) := by
    rw [qc_eq_exp, ← Complex.exp_neg]
  rw [h1, qc_eq_exp]
  push_cast
  rw [Complex.cos, neg_mul]
  ring

/-! ### Diagonalisation of the adjacency matrix of `C₁₃` -/

/-- The adjacency matrix of the 13-cycle, over `ℂ`. -/
