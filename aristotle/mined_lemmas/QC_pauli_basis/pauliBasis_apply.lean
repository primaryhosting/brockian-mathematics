/-
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The identity Pauli matrix `I`. -/

@[simp] lemma pauliBasis_apply (i : Fin 4) : pauliBasis i = pauli i :=
  Module.Basis.mk_apply _ _ _

/-- **Pauli basis**: the family `![I, X, Y, Z]` is linearly independent over `ℂ` and spans
the space of `2 × 2` complex matrices, i.e. it is a basis of that `ℂ`-vector space. -/
