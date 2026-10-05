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

def classicalExp {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) : ℚ :=
  if ∀ j, (simulate C (pauliZ k)).x j = false then
    phaseQ (simulate C (pauliZ k)).ph * sgnQ (simulate C (pauliZ k)).z b
  else 0

/-- The classical simulation algorithm: it computes, by tableau updates only, the probability
that measuring qubit `k` at the end of the circuit `C` applied to `|b⟩` yields `0`. -/
