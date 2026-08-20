/-
# Pauli Anticommute
Category: Quantum Computing
Target: QC.pauli_anticommute
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` matrix. -/

private lemma pauli_ext_iff (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A = B ↔ A 0 0 = B 0 0 ∧ A 0 1 = B 0 1 ∧ A 1 0 = B 1 0 ∧ A 1 1 = B 1 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;> assumption

/-- `X * X = 1`. -/
