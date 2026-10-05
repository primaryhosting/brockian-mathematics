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

lemma pauliZ_mat {n : ℕ} (k : Fin n) :
    pauliMat (pauliZ k) = Matrix.diagonal (fun a : BasisState n => if a k then -1 else 1) := by
  ext a b
  have hsgn : sgnQ (fun j => decide (j = k)) b = if b k then -1 else 1 := by
    unfold sgnQ
    rw [Finset.prod_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [pauliMat_apply, Matrix.diagonal_apply]
  show (if (∀ j, a j = xor (b j) false) then _ else _) = _
  by_cases h : a = b
  · subst h
    rw [if_pos (fun j => by simp), if_pos rfl]
    simp only [pauliZ, iPow_zero, one_mul, hsgn]
    by_cases hb : a k <;> simp [hb]
  · rw [if_neg h]
    refine if_neg ?_
    intro hall
    exact h (funext fun j => by simpa using hall j)

/-- The Heisenberg-evolved observable `U† Zₖ U` is exactly the Pauli produced by the classical
tableau simulation. -/
