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

lemma tens_update_smul {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) (k : Fin n) (c : ℂ)
    (M : Matrix Bool Bool ℂ) :
    tens (Function.update f k (c • M)) = c • tens (Function.update f k M) := by
  ext a b
  simp only [tens_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have key : ∀ j ∈ Finset.univ.erase k,
      (Function.update f k (c • M)) j (a j) (b j) = (Function.update f k M) j (a j) (b j) := by
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
  rw [Finset.prod_congr rfl key]
  simp only [Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## One-qubit matrices -/

/-- `1/√2`, as a complex number. -/
