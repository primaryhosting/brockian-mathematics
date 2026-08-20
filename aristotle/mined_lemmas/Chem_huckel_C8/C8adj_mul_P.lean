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

lemma C8adj_mul_P : C8adj * P = P * D := by
  ext i k
  rw [Matrix.mul_apply, C8adj_row_sum, D, Matrix.mul_diagonal, P_apply, P_apply, P_apply]
  exact om_key i k

