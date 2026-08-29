import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate
open scoped InnerProductSpace

namespace QI

/-! ## Setup

Nine qubits, indexed by `Idx = Fin 3 × Fin 3`: the first component is the block
(one of the three "outer" repetition-code slots), the second is the position of the
qubit inside its block.  A computational basis state is a bit string `Idx → Bool`,
and the state space is the corresponding `512`-dimensional complex Hilbert space. -/

/-- Index of a qubit: `(block, position within block)`. -/
abbrev Idx := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits. -/
abbrev BasisIdx := Idx → Bool

/-- The nine-qubit state space. -/
abbrev QState := EuclideanSpace ℂ BasisIdx

/-- The operator acting as the `2 × 2` matrix `M` on qubit `q` and as the identity
on the remaining eight qubits.  Every single-qubit error on qubit `q` is of this form. -/

theorem shor_code_detects_Z (q : Idx) (a b : Bool) :
    ⟪codeword a, qubitOp q pauliZ (codeword b)⟫_ℂ = 0 :=
  shor_code_detects_traceless q pauliZ (by simp [pauliZ]) a b

end QI

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

