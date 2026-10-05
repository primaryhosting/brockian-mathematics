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

namespace QC

open Complex Finset

/-- The scalar `1/√2`, the normalization constant of the Bell states. -/

noncomputable def postMeasure (psi : Bool → ℂ) (a b : Bool) (k : Bool) : ℂ :=
  2 * ∑ i : Bool, ∑ j : Bool, (starRingEnd ℂ) (bell a b i j) * inputState psi i j k

/-- Bob's correction, applying the Pauli operator `Z^a X^b` to his qubit. -/
