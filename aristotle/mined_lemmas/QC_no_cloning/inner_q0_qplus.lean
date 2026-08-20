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

lemma inner_q0_qplus : ⟪q0, qplus⟫_ℂ = ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [q0, qplus, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]

/-- **No-cloning, isometry version.** There is no linear isometry `U` of the two-qubit space
which maps `|ψ⟩ ⊗ |z⟩` to `|ψ⟩ ⊗ |ψ⟩` for every unit vector `|ψ⟩`, whatever the (unit) blank
state `|z⟩` is. -/
