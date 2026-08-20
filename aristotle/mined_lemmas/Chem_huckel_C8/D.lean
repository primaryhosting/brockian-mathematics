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

noncomputable def D : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (fun k : Fin 8 => (C8eig k : ℂ))

/-- The pointwise eigenvalue relation for the circulant structure. -/
