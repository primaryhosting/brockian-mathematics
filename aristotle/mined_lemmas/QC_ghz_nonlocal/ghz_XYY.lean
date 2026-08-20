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

theorem ghz_XYY : (op3 pauliX pauliY pauliY) *ᵥ ghz = -ghz := by
  funext p
  fin_cases p <;>
    simp [op3, ghz, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      pauliX, pauliY, Matrix.kroneckerMap]

