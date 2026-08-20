import Mathlib

/-!
# Superdense coding

Alice and Bob share the maximally entangled Bell pair
`|Φ+⟩ = (|00⟩ + |11⟩)/√2` (Alice holds the first qubit, Bob the second).
To send two classical bits `(a, b)` Alice applies the local unitary
`X^a Z^b` to *her* qubit only, i.e. the operator `X^a Z^b ⊗ I` acts on the pair,
and she then sends that single qubit to Bob.

We show that the four resulting two–qubit states are orthonormal, hence perfectly
distinguishable by Bob, and in particular that the encoding map is injective on
the four two–bit messages: two classical bits are transmitted by sending one
qubit.
-/

namespace QC

open Matrix
open scoped Kronecker

/-- A two–qubit state vector, indexed by a pair of bits. -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Pauli `X` matrix. -/

theorem superdense_two_bits : Function.Injective encode := by
  intro m m' h
  by_contra hne
  have h0 : ip (encode m) (encode m') = 0 := encode_orthogonal hne
  rw [h, encode_normalized m'] at h0
  exact one_ne_zero h0

end QC

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

