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

/-- Bit flip on a single (qu)bit index. -/

noncomputable def postMeasure (psi : Fin 2 → ℂ) (i j : Fin 2) (c : Fin 2) : ℂ :=
  2 * ∑ a : Fin 2, ∑ b : Fin 2, star (bellBasis i j a b) * initialState psi a b c

/-- The Pauli `X` gate. -/
