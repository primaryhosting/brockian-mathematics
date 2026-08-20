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

lemma om_pow_eq_exp (k : ℕ) :
    om ^ k = Complex.exp ((2 * Real.pi * k / 8 : ℝ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to index `k`. -/
