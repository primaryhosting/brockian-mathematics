/-
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open scoped ComplexConjugate

/-- The state space of two qubits, `ℂ² ⊗ ℂ²`, modelled as the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)`: functions on pairs of bits with the standard
Hermitian inner product.  The basis vector indexed by `(a, b)` is the product state
`|a⟩ ⊗ |b⟩`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The product state `|a⟩ ⊗ |b⟩` of two qubit basis states. -/

theorem inner_eq (x y : TwoQubit) :
    inner ℂ x y = ∑ p : Fin 2 × Fin 2, conj (x.ofLp p) * y.ofLp p := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

