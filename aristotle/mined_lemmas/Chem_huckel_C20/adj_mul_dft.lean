/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma adj_mul_dft : adjC20 * dftMat = dftMat * diagC20 := by
  ext i k
  rw [Matrix.mul_apply, adj_row_sum (fun j => dftMat j k) i]
  simp only [dftMat, Matrix.of_apply, diagC20, Matrix.mul_diagonal]
  have h1 : (i - 1) * k = i * k + (-k) := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  rw [h1, h2, e_add, e_add, ← mul_add, e_neg, show e k = om ^ k.val from rfl,
    add_comm (om ^ (19 * k.val)) (om ^ k.val), om_two_cos]

