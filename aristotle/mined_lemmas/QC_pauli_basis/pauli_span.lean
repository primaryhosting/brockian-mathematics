import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/

lemma pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨![(M 0 0 + M 1 1) / 2, (M 0 1 + M 1 0) / 2,
      Complex.I * (M 0 1 - M 1 0) / 2, (M 0 0 - M 1 1) / 2], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, pauli, pauliI, pauliX, pauliY, pauliZ] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-- **The Pauli matrices form a basis of the ℂ-vector space of 2×2 complex matrices.**
The family `{I, X, Y, Z}` is linearly independent and spans `Matrix (Fin 2) (Fin 2) ℂ`. -/
