/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The Hadamard matrix entry `H a b = (-1)^(a ∧ b) / √2`. -/

lemma deutschFinal_true (f : Bool → Bool) (y : Bool) :
    deutschFinal f (true, y) =
      ((if xor y (f false) then -1 else 1) - (if xor y (f true) then -1 else 1)) /
        ((Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ)) := by
  simp only [deutschFinal, applyH1, oracle, applyH2, psi0, had, Fintype.sum_bool,
    Fintype.sum_prod_type]
  norm_num
  field_simp
  ring

/-- **Deutsch's algorithm is correct.** With a single query to the oracle for
`f : Bool → Bool`, measuring the first qubit of the final state yields `0` with
probability `1` exactly when `f` is constant, and `1` with probability `1`
exactly when `f` is balanced. -/
