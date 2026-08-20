import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QI

/-- A single qubit: the two-dimensional complex Hilbert space `ℂ²`. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- Two qubits: the Hilbert space `ℂ² ⊗ ℂ² ≃ ℂ^(2×2)`. -/
abbrev TwoQubits : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor (Kronecker) product of two qubit states. -/

theorem inner_ket0_ketS : ⟪ket0, ketS⟫_ℂ = 3 / 5 := by
  simp [ket0, ketS, PiLp.inner_apply, Fin.sum_univ_two]

/-- **No-deleting theorem** (strong form).  There is no linear isometry `U` of the two-qubit
space and no fixed "blank" state `blank` such that `U` maps `|ψ⟩ ⊗ |ψ⟩` to `|ψ⟩ ⊗ |blank⟩`
for every unit vector `|ψ⟩`; i.e. no machine can delete one of two copies of an unknown
quantum state. -/
