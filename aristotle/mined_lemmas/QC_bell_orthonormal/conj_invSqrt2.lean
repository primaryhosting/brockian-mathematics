import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

open scoped TensorProduct

/-- A single qubit space: `ℂ²` with its standard Hermitian inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`. Mathlib equips a tensor product of inner product spaces
with the inner product determined by `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis vectors `|0⟩`, `|1⟩` of a single qubit. -/

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
