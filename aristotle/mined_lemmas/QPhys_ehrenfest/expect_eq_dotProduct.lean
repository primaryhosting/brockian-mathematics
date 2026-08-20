/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex Matrix

namespace QPhys

variable {n : ℕ}

/-- The expectation value `⟨v, M v⟩` of the (matrix) observable `M` in the state `v`. -/

lemma expect_eq_dotProduct (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    expect M v = star v ⬝ᵥ (M *ᵥ v) := by
  simp [expect, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

