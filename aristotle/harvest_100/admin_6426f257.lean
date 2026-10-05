/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a `/-!` module docstring before `import`; the header is repeated
-- verbatim as a module docstring immediately after the imports below.)

import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
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

/-!
## Setup

A qubit is a vector in `ℂ²`, which we index by `Bool` (`false = |0⟩`, `true = |1⟩`).
The three qubits of the teleportation protocol are: Alice's unknown input qubit `ψ`,
Alice's half of an EPR pair, and Bob's half of that pair.
-/

/-- The scalar `1/√2`, as a complex number. -/
noncomputable def sqrt2inv : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma sqrt2inv_sq : sqrt2inv * sqrt2inv = 1 / 2 := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  unfold sqrt2inv
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, h]
  norm_num

@[simp] lemma conj_sqrt2inv : (starRingEnd ℂ) sqrt2inv = sqrt2inv := by
  simp [sqrt2inv]

/-- The Pauli `X` (bit-flip) gate. -/
def pauliX : Matrix Bool Bool ℂ := Matrix.of fun i j => if i = j then 0 else 1

/-- The Pauli `Z` (phase-flip) gate. -/
def pauliZ : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i = j then (if i then -1 else 1) else 0

/-- The EPR pair `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` shared by Alice (index `j`) and Bob (index `k`). -/
noncomputable def bellPair : Bool → Bool → ℂ := fun j k => if j = k then sqrt2inv else 0

/-- The Bell basis state `|B_{a,b}⟩ = (|0, b⟩ + (-1)^a |1, ¬b⟩)/√2` of Alice's two qubits,
labelled by the two classical bits `a, b` of the measurement outcome. -/
noncomputable def bellBasis (a b : Bool) : Bool → Bool → ℂ :=
  fun i j => sqrt2inv * (if j = xor i b then (if a && i then -1 else 1) else 0)

/-- The three-qubit state `|ψ⟩ ⊗ |Φ⁺⟩` at the start of the protocol: index `i` is Alice's
input qubit, index `j` is Alice's half of the EPR pair, index `k` is Bob's half. -/
noncomputable def totalState (psi : Bool → ℂ) : Bool → Bool → Bool → ℂ :=
  fun i j k => psi i * bellPair j k

/-- Bob's (renormalised) qubit after Alice measures her two qubits in the Bell basis and
obtains the outcome `(a, b)`: it is the partial inner product `(⟨B_{a,b}| ⊗ I) |ψ ⊗ Φ⁺⟩`,
rescaled by the factor `2 = 1/√(1/4)` coming from the outcome probability `1/4`. -/
noncomputable def postMeasurement (psi : Bool → ℂ) (a b : Bool) : Bool → ℂ :=
  fun k => 2 * ∑ i : Bool, ∑ j : Bool,
    (starRingEnd ℂ) (bellBasis a b i j) * totalState psi i j k

/-- The unitary correction `Z^a X^b` that Bob applies after receiving the two classical
bits `(a, b)` from Alice. -/
noncomputable def correction (a b : Bool) : Matrix Bool Bool ℂ :=
  (if a then pauliZ else 1) * (if b then pauliX else 1)

/-- After Alice's Bell measurement yields the outcome `(a, b)`, Bob's (renormalised)
qubit is exactly `X^b Z^a ψ`. -/
theorem postMeasurement_eq (psi : Bool → ℂ) (a b : Bool) :
    postMeasurement psi a b =
      ((if b then pauliX else 1) * (if a then pauliZ else 1)).mulVec psi := by
  funext k
  simp only [postMeasurement, totalState, bellBasis, bellPair, pauliX, pauliZ,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool]
  cases a <;> cases b <;> cases k <;>
    simp [mul_comm, mul_assoc] <;>
    rw [← mul_assoc, sqrt2inv_sq] <;> ring

/-- **Teleportation identity.** For every input qubit `ψ` and every Bell-measurement
outcome `(a, b)`, applying Bob's correction `Z^a X^b` to his post-measurement state
returns exactly the input state `ψ`. -/
theorem teleportation_identity (psi : Bool → ℂ) (a b : Bool) :
    (correction a b).mulVec (postMeasurement psi a b) = psi := by
  funext k
  simp only [correction, postMeasurement, totalState, bellBasis, bellPair, pauliX, pauliZ,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool]
  cases a <;> cases b <;> cases k <;>
    simp [mul_comm, mul_assoc, mul_left_comm] <;>
    rw [← mul_assoc, sqrt2inv_sq] <;> ring

end QC

