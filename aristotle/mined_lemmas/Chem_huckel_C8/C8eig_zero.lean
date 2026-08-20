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

lemma C8eig_zero : C8eig 0 = 2 := by norm_num [C8eig]

