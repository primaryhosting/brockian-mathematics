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

private theorem inv_sqrt_two_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The four Bell states are orthonormal. -/
