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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

/-! ## Basis states and tensor products of one-qubit operators -/

/-- A computational basis state of `n` qubits. -/
abbrev BasisState (n : ℕ) := Fin n → Bool

/-- An operator on `n` qubits, as a `2^n × 2^n` complex matrix. -/
abbrev Op (n : ℕ) := Matrix (BasisState n) (BasisState n) ℂ

/-- The tensor product `f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (n-1)` of one-qubit operators. -/

def step {n : ℕ} : Gate n → Pauli n → Pauli n
  | Gate.H k, p =>
      { ph := p.ph + (if p.x k && p.z k then 2 else 0)
        x := Function.update p.x k (p.z k)
        z := Function.update p.z k (p.x k) }
  | Gate.S k, p =>
      { ph := p.ph + (if p.x k then 3 else 0)
        x := p.x
        z := Function.update p.z k (xor (p.z k) (p.x k)) }
  | Gate.CZ k l _, p =>
      { ph := p.ph + (if p.x k && p.x l then 2 else 0)
        x := p.x
        z := Function.update (Function.update p.z k (xor (p.z k) (p.x l))) l
              (xor (p.z l) (p.x k)) }

/-! ## One-qubit conjugation identities -/

