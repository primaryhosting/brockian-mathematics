/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A single-qubit state is a complex amplitude function on the computational basis
`{|0⟩, |1⟩}`, indexed by `Bool` (`false ↦ |0⟩`, `true ↦ |1⟩`). -/
abbrev Qubit := Bool → ℂ

/-- The scalar `1/√2`, as a complex number. -/

lemma postMeasurement_normSq (psi : Qubit) (m n : Bool) :
    ∑ k : Bool, Complex.normSq (postMeasurement m n (initialState psi) k) =
      (1 / 4) * ∑ i : Bool, Complex.normSq (psi i) := by
  simp only [postMeasurement_initialState, Fintype.sum_bool]
  cases m <;> cases n <;>
    simp [Complex.normSq_mul, Complex.normSq_neg] <;> ring

/-- The Pauli `X` (bit-flip) correction, applied when the classical bit `n` is `true`. -/
