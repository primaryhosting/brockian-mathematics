/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped ComplexConjugate

namespace QC

/-- The state space of two qubits, `ℂ² ⊗ ℂ²`, realized concretely as the
finite-dimensional Hilbert space `EuclideanSpace ℂ (Fin 2 × Fin 2)`, whose standard basis
is the computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The normalization constant `1/√2`. -/

lemma inner_bell_eq_ite (i j : Fin 4) :
    inner ℂ (bell i) (bell j) = if i = j then 1 else 0 := by
  rw [inner_bell]
  fin_cases i <;> fin_cases j <;>
    simp [bellCoord, Fintype.sum_prod_type, Fin.sum_univ_succ, conj_invSqrt2,
      invSqrt2_mul_self] <;>
    ring

/-- The four Bell states are orthonormal. -/
