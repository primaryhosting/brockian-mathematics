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

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
