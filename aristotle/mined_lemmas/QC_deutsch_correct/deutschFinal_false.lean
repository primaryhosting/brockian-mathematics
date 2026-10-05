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

lemma deutschFinal_false (f : Bool → Bool) (y : Bool) :
    deutschFinal f (false, y) =
      ((if xor y (f false) then -1 else 1) + (if xor y (f true) then -1 else 1)) /
        ((Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ)) := by
  simp only [deutschFinal, applyH1, oracle, applyH2, psi0, had, Fintype.sum_bool,
    Fintype.sum_prod_type]
  norm_num
  field_simp
  ring

/-- Explicit amplitudes of the final state on the first-qubit-`true` branch. -/
