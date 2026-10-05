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

lemma sum_normSq {n : ℕ} (C : List (Gate n)) (b : BasisState n) :
    ∑ a : BasisState n, ‖circMat C a b‖ ^ 2 = 1 := by
  have h1 : ((circMat C)ᴴ * circMat C) b b = 1 := by
    rw [circ_unitary]; simp
  rw [Matrix.mul_apply] at h1
  have h2 : ∀ a : BasisState n,
      (circMat C)ᴴ b a * circMat C a b = ((‖circMat C a b‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Matrix.conjTranspose_apply, star_mul_self_ofReal]
  rw [Finset.sum_congr rfl (fun a _ => h2 a)] at h1
  exact_mod_cast h1

/-- The expectation value of `Zₖ` in the output state equals the classically computed value. -/
