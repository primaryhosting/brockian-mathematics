/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

lemma Pmat_apply (i k : Fin 10) : Pmat i k = zeta ^ ((i : ℕ) * (k : ℕ)) := by
  simp [Pmat, Matrix.vandermonde_apply, ← pow_mul]

/-- The key row identity: the two cyclic neighbours contribute the eigenvalue factor. -/
