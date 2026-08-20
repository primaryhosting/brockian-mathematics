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

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 10 := by
  have := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  simpa [zeta] using this

