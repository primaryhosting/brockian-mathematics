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

lemma P_det_ne_zero : P.det ≠ 0 := by
  rw [P, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have := isPrimitiveRoot_om.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

/-- The diagonal matrix of eigenvalues. -/
