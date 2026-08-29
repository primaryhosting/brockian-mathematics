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

lemma sgnQ_eq_pm {n : ℕ} (z b : BasisState n) : sgnQ z b = 1 ∨ sgnQ z b = -1 := by
  classical
  unfold sgnQ
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => left; simp
  | insert j s hj ih =>
      rw [Finset.prod_insert hj]
      rcases ih with h | h <;> rw [h] <;>
        [skip; skip] <;> by_cases hz : z j && b j <;> simp [hz]

