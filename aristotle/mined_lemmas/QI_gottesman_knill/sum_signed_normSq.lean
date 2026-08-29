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

lemma sum_signed_normSq {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) :
    ∑ a : BasisState n, (if a k then (-1 : ℝ) else 1) * ‖circMat C a b‖ ^ 2
      = ((classicalExp C b k : ℚ) : ℝ) := by
  have h1 := conj_pauliZ C k
  rw [pauliZ_mat] at h1
  have h2 : ((circMat C)ᴴ * (Matrix.diagonal (fun a : BasisState n => if a k then -1 else 1) :
      Op n) * circMat C) b b = ((classicalExp C b k : ℚ) : ℂ) := by
    rw [h1, pauli_diag_eq]
  rw [Matrix.mul_apply] at h2
  have h3 : ∀ a : BasisState n,
      ((circMat C)ᴴ * (Matrix.diagonal (fun a : BasisState n => if a k then -1 else 1) : Op n))
          b a * circMat C a b
        = (((if a k then (-1 : ℝ) else 1) * ‖circMat C a b‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    have : star (circMat C a b) * circMat C a b = ((‖circMat C a b‖ ^ 2 : ℝ) : ℂ) :=
      star_mul_self_ofReal _
    by_cases h : a k
    · rw [if_pos h, if_pos h]
      push_cast
      rw [mul_comm (star (circMat C a b)) (-1 : ℂ), mul_assoc, this]
      push_cast
      ring
    · rw [if_neg h, if_neg h]
      push_cast
      rw [mul_one, this]
      push_cast
      ring
  rw [Finset.sum_congr rfl (fun a _ => h3 a)] at h2
  exact_mod_cast h2

/-- **Gottesman–Knill**: stabilizer circuits are efficiently classically simulable.

For every `n`-qubit stabilizer (Clifford) circuit `C` built from Hadamard, phase and
controlled-`Z` gates, every computational basis input `|b⟩` and every qubit `k`, the exact
quantum probability that measuring qubit `k` of the output state `U_C |b⟩` yields the outcome
`0` — computed from the genuine `2^n × 2^n` complex unitary `U_C` — is equal to the rational
number produced by the purely classical tableau algorithm `classicalProb`, whose running cost
`simCost C` is linear (hence polynomial) in the number of gates and the number of qubits. -/
