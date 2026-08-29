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

lemma C10_mul_F : C10 * F = F * Matrix.diagonal mu := by
  ext i k
  have hL : (C10 * F) i k = (C10 *ᵥ fun j => F j k) i := rfl
  rw [hL, C10_mulVec, Matrix.mul_diagonal]
  simpa [F, ← zk_add_inv k, zk_inv_eq k] using pow_shift_eq (zk k) (zk_pow_ten k) i

