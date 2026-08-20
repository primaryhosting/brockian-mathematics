/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header above is a plain block comment and is repeated as a doc comment below.)

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

/-! ### Values of `cos (2πm/4)` -/

/-- `cos (2πm/4)` only depends on `m % 4`. -/

theorem eig_two :
    A4.mulVec (v4 2) = (2 * Real.cos (2 * π * ((2 : Fin 4) : ℕ) / 4)) • v4 2 := by
  rw [v4_two]
  funext j; fin_cases j <;>
    simp [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, cosB] <;> norm_num

