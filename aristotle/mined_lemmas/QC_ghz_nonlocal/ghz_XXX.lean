/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Complex
open scoped Kronecker

/-- The Pauli `X` matrix. -/

theorem ghz_XXX : (op3 pauliX pauliX pauliX) *ᵥ ghz = ghz := by
  funext p
  fin_cases p <;>
    simp [op3, ghz, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      pauliX, Matrix.kroneckerMap]

/-- Mermin's algebraic contradiction: no assignment of definite `±1` values `x i` (for the
`X` measurement on qubit `i`) and `y i` (for the `Y` measurement on qubit `i`) can reproduce
the GHZ correlations `XYY = YXY = YYX = -1`, `XXX = +1`. -/
