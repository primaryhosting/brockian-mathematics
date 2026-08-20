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

/-!
# Superdense coding

Superdense coding: Alice and Bob share the maximally entangled two-qubit state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.  To send two classical bits `(a, b)` Alice applies the local
unitary `Z^a X^b` to *her* qubit only (the first tensor factor) and sends that single qubit
to Bob.  The four resulting global states are the four Bell states.

We model a two-qubit pure state as a function `Fin 2 × Fin 2 → ℂ` (amplitudes in the
computational basis) and Alice's local operation as left multiplication of the first index
by a `2 × 2` matrix.

The main result `QC.superdense_two_bits` says that the encoding of the four messages
(elements of `Bool × Bool`, i.e. two classical bits) is injective; `QC.encode_orthonormal`
strengthens this to: the four encoded states are orthonormal, hence perfectly
distinguishable by Bob, so two classical bits are indeed transmitted.
-/

namespace QC

open Matrix

/-- The Pauli `X` matrix. -/

noncomputable def encU (m : Bool × Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if m.1 then PZ else 1) * (if m.2 then PX else 1)

/-- Alice's encoding operations are unitary. -/
