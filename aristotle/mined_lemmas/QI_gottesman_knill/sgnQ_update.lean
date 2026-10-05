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

lemma sgnQ_update {n : ℕ} (z b : BasisState n) (k : Fin n) (v : Bool) :
    sgnQ (Function.update z k v) b = (if xor v (z k) && b k then -1 else 1) * sgnQ z b := by
  unfold sgnQ
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have key : ∀ j ∈ Finset.univ.erase k,
      (if (Function.update z k v) j && b j then (-1 : ℚ) else 1)
        = (if z j && b j then (-1 : ℚ) else 1) := by
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [Finset.prod_congr rfl key, Function.update_self, ← mul_assoc]
  congr 1
  cases v <;> cases hz : z k <;> cases hb : b k <;> norm_num

