/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma C14vand_det_ne_zero : C14vand.det ≠ 0 := by
  rw [C14vand, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (w14_primitive.pow_inj a.isLt b.isLt hab)

