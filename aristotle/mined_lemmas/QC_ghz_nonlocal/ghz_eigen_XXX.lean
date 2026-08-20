/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Matrix

namespace QC

/-! ## The quantum side: the GHZ state and its Pauli eigenvalue relations -/

/-- Index type for a three-qubit computational basis. -/
abbrev Idx := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` observable. -/

theorem ghz_eigen_XXX : tensor3 pauliX pauliX pauliX *ᵥ ghz = -ghz := by
  funext i
  obtain ⟨a, b, c⟩ := i
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      tensor3, pauliX, ghz]

/-! ## The classical side: local hidden variables cannot match those predictions -/

/-- **Mermin's argument.**

A local hidden-variable model assigns, for each party (`A`, `B`, `C`) and each of the two
measurement settings (`false` = the `X` observable, `true` = the `Y` observable), a
predetermined outcome `±1` that does not depend on the settings chosen by the other parties.

No such assignment reproduces all four GHZ correlations
`XYY = YXY = YYX = +1` and `XXX = -1`: multiplying the first three relations gives
`A X * B X * C X = +1` (each `Y` outcome occurs twice and squares to `1`), which
contradicts the fourth. -/
