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

noncomputable def kron (ψ φ : Qubit) : TwoQubits :=
  WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => ψ.ofLp p.1 * φ.ofLp p.2)

/-- The inner product on the two-qubit space factorises on product states. -/
