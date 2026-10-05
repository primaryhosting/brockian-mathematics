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

lemma det_F_ne_zero : F.det ≠ 0 := by
  have hT : Fᵀ = Matrix.vandermonde zk := by
    ext k i; simp [F, Matrix.vandermonde]
  rw [← Matrix.det_transpose, hT]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr zk_injective

