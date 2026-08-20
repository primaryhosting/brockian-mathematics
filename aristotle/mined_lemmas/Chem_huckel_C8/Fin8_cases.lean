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

lemma Fin8_cases (k : Fin 8) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
  fin_cases k <;> decide

/-- The Hückel spectrum of `C₈` in closed form: the eigenvalues of the adjacency matrix of
the cycle `C₈` are exactly `2, √2, 0, -√2, -2` (the values `2 cos (2πk/8)`, `k = 0,…,7`). -/
