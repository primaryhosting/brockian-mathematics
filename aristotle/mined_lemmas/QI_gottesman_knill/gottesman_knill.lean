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

theorem gottesman_knill {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) :
    measProb C b k = ((classicalProb C b k : ℚ) : ℝ) ∧
      simCost C ≤ 3 * C.length + 2 * n + 2 := by
  refine ⟨?_, le_of_eq (simCost_eq C)⟩
  have hsplit : ∑ a : BasisState n, (if a k then (0 : ℝ) else ‖circMat C a b‖ ^ 2)
      = ((∑ a : BasisState n, ‖circMat C a b‖ ^ 2)
          + ∑ a : BasisState n, (if a k then (-1 : ℝ) else 1) * ‖circMat C a b‖ ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : a k <;> simp [h]
  rw [measProb, hsplit, sum_normSq, sum_signed_normSq, classicalProb]
  push_cast
  ring

end QI

