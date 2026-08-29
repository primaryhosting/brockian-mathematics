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

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, h]; norm_num
  rw [invSqrt2, ← mul_inv, h2]
  norm_num

