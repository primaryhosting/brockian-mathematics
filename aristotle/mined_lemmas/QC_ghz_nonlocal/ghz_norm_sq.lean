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

theorem ghz_norm_sq : ∑ i, Complex.normSq (ghz i) = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ, ghz, Complex.normSq_apply]
  nlinarith [h2]

/-- Quantum prediction: `X ⊗ Y ⊗ Y` has the GHZ state as a `+1` eigenvector. -/
