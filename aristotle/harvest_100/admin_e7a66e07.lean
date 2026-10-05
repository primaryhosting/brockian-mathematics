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
noncomputable def had (a b : Bool) : ℂ := (if a && b then -1 else 1) / (Real.sqrt 2 : ℝ)

/-- The initial two–qubit state `|0⟩|1⟩`, as an amplitude function on `Bool × Bool`. -/
noncomputable def psi0 : Bool × Bool → ℂ := fun p => if p = (false, true) then 1 else 0

/-- Apply a Hadamard gate to each of the two qubits. -/
noncomputable def applyH2 (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => ∑ q : Bool × Bool, had p.1 q.1 * had p.2 q.2 * psi q

/-- Apply a Hadamard gate to the first qubit only. -/
noncomputable def applyH1 (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => ∑ x : Bool, had p.1 x * psi (x, p.2)

/-- The oracle `U_f |x, y⟩ = |x, y ⊕ f x⟩`, acting on amplitude functions. -/
noncomputable def oracle (f : Bool → Bool) (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => psi (p.1, xor p.2 (f p.1))

/-- The final state of Deutsch's algorithm: prepare `|0⟩|1⟩`, apply `H ⊗ H`,
query the oracle once, then apply `H` to the first qubit. -/
noncomputable def deutschFinal (f : Bool → Bool) : Bool × Bool → ℂ :=
  applyH1 (oracle f (applyH2 psi0))

/-- The probability of observing `b` when measuring the first qubit of the final state. -/
noncomputable def probFirst (f : Bool → Bool) (b : Bool) : ℝ :=
  ∑ y : Bool, ‖deutschFinal f (b, y)‖ ^ 2

/-- Explicit amplitudes of the final state on the first-qubit-`false` branch. -/
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
theorem deutsch_correct (f : Bool → Bool) :
    probFirst f false = (if f false = f true then 1 else 0) ∧
    probFirst f true = (if f false = f true then 0 else 1) := by
  have h2 : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 :=
    Real.mul_self_sqrt (by norm_num)
  constructor <;>
  · simp only [probFirst, Fintype.sum_bool, deutschFinal_false, deutschFinal_true]
    cases hf0 : f false <;> cases hf1 : f true <;>
      simp [div_pow, h2, mul_pow] <;> norm_num

#print axioms QC.deutsch_correct

end QC

