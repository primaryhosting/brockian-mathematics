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

lemma C8adj_row_sum (i k : Fin 8) :
    ∑ j : Fin 8, C8adj i j * P j k = P (i + 1) k + P (i - 1) k := by
  fin_cases i <;>
    simp +decide [C8adj, Fin.sum_univ_eight, Matrix.of_apply,
      show (-1 : Fin 8) = 7 from rfl] <;> exact add_comm _ _

