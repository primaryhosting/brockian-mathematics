/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

def unitVec {n : ℕ} (i : Fin n) : Bits n := Pi.single i 1

/-! ## The Pauli group -/

/-- An element of the `n`-qubit Pauli group, written as `i^ph * X^xs * Z^zs`. -/
structure Pauli (n : ℕ) where
  /-- The power of `i` multiplying the Pauli monomial. -/
  ph : ZMod 4
  /-- The `X`-part exponents. -/
  xs : Bits n
  /-- The `Z`-part exponents. -/
  zs : Bits n
deriving DecidableEq

/-- The `2^n × 2^n` complex matrix of a Pauli group element:
`i^ph X^xs Z^zs |x⟩ = i^ph (-1)^(zs ⬝ x) |x + xs⟩`. -/
