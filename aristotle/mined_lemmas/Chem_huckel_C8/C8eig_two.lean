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

lemma C8eig_two : C8eig 2 = 0 := by
  rw [C8eig, show (2 * Real.pi * ((2 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi / 2 by norm_num; ring,
    Real.cos_pi_div_two]
  ring

