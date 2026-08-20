import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ComplexConjugate InnerProductSpace

namespace QC

/-- The state space of one qubit, `ℂ²` with the Euclidean (Hilbert) structure. -/
noncomputable abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `Qubit ⊗ Qubit` realized concretely as
functions on `Fin 2 × Fin 2`. -/
noncomputable abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product of two qubit states. -/

lemma inner_tens (a b c d : Qubit) :
    ⟪tens a b, tens c d⟫_ℂ = ⟪a, c⟫_ℂ * ⟪b, d⟫_ℂ := by
  simp only [tens, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
    Finset.sum_mul_sum]
  simp [map_mul, mul_mul_mul_comm]

/-- The computational basis state `|0⟩`. -/
