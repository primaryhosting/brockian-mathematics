import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
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

/-- The 2×2 identity (Pauli `I`). -/

@[simp] lemma coe_pauliBasis : ⇑pauliBasis = pauli := Module.Basis.coe_mk _ _

/-- **Pauli basis.** The four Pauli matrices `I, X, Y, Z` are linearly independent over `ℂ`
and span the space of 2×2 complex matrices; hence they form a basis, witnessed by
`QC.pauliBasis`. -/
