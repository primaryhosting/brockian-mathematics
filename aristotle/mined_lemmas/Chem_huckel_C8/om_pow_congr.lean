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

lemma om_pow_congr {m n : ℕ} (h : m % 8 = n % 8) : om ^ m = om ^ n := by
  rw [om_pow_mod m, om_pow_mod n, h]

/-- `om ^ k` equals `exp (θ I)` where `θ = 2πk/8`. -/
