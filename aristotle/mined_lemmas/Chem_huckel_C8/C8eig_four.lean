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

lemma C8eig_four : C8eig 4 = -2 := by
  rw [C8eig, show (2 * Real.pi * ((4 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi by norm_num; ring,
    Real.cos_pi]
  ring

