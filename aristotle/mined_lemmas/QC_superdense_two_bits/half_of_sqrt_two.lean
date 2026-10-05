import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- A two-qubit state: `ψ (i, j)` is the amplitude of the basis state `|i⟩ ⊗ |j⟩`.
The first factor is Alice's qubit, the second is Bob's. -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Bell state `(|00⟩ + |11⟩)/√2`, shared in advance between Alice and Bob. -/

private theorem half_of_sqrt_two :
    ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
  have h : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← Complex.ofReal_mul, h]
  norm_num

/-- The four encoded states form an orthonormal family: Bob can distinguish them
perfectly by a measurement in the Bell basis. -/
