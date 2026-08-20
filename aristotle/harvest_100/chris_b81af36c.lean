/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-!
## Deutsch's algorithm

A two–qubit state is modelled as an amplitude function `Bool → Bool → ℂ`, where the first
argument is the query register and the second the answer register.

The algorithm is:

* prepare `|0⟩|1⟩`;
* apply a Hadamard gate to each qubit;
* apply the oracle `U_f : |x⟩|y⟩ ↦ |x⟩|y ⊕ f x⟩` **once**;
* apply a Hadamard gate to the first qubit;
* measure the first qubit.

`QC.prob0 f` is the probability of observing `0` in the first register.  The theorem
`QC.deutsch_correct` says that this probability is `1` exactly when `f` is constant and `0`
exactly when `f` is balanced, so a single oracle query decides constant vs balanced.
-/

namespace QC

/-- The sign `(-1)^b`. -/
noncomputable def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- The Hadamard normalisation factor `1/√2`. -/
noncomputable def hcoe : ℝ := (Real.sqrt 2)⁻¹

/-- Hadamard gate on the first qubit. -/
noncomputable def H1 (ψ : Bool → Bool → ℂ) : Bool → Bool → ℂ :=
  fun z y => (hcoe : ℂ) * ∑ x : Bool, sgn (x && z) * ψ x y

/-- Hadamard gate on the second qubit. -/
noncomputable def H2 (ψ : Bool → Bool → ℂ) : Bool → Bool → ℂ :=
  fun x w => (hcoe : ℂ) * ∑ y : Bool, sgn (y && w) * ψ x y

/-- The phase-oracle-free (standard) oracle `|x⟩|y⟩ ↦ |x⟩|y ⊕ f x⟩`, acting on amplitudes. -/
def oracle (f : Bool → Bool) (ψ : Bool → Bool → ℂ) : Bool → Bool → ℂ :=
  fun x y => ψ x (xor y (f x))

/-- The initial state `|0⟩|1⟩`. -/
noncomputable def init : Bool → Bool → ℂ := fun x y => if x = false ∧ y = true then 1 else 0

/-- The state produced by Deutsch's algorithm, using exactly one oracle query. -/
noncomputable def deutschState (f : Bool → Bool) : Bool → Bool → ℂ :=
  H1 (oracle f (H1 (H2 init)))

/-- The probability of measuring `0` in the first register. -/
noncomputable def prob0 (f : Bool → Bool) : ℝ :=
  ‖deutschState f false false‖ ^ 2 + ‖deutschState f false true‖ ^ 2

/-- `f` is constant. -/
def IsConstant (f : Bool → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced, i.e. it takes both values. -/
def IsBalanced (f : Bool → Bool) : Prop := f false ≠ f true

lemma hcoe_sq : hcoe ^ 2 = 1 / 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [hcoe, inv_pow, h]

lemma hcoe_nonneg : 0 ≤ hcoe := by
  simp [hcoe, Real.sqrt_nonneg]

/-- Closed form for the amplitudes of the first register being `0`. -/
lemma deutschState_false (f : Bool → Bool) (y : Bool) :
    deutschState f false y = (hcoe : ℂ) ^ 3 * sgn y * (sgn (f false) + sgn (f true)) := by
  cases y <;> cases hy0 : f false <;> cases hy1 : f true <;>
    simp [deutschState, H1, H2, oracle, init, sgn, hy0, hy1] <;> ring

/-- Closed form for the amplitudes of the first register being `1`. -/
lemma deutschState_true (f : Bool → Bool) (y : Bool) :
    deutschState f true y = (hcoe : ℂ) ^ 3 * sgn y * (sgn (f false) - sgn (f true)) := by
  cases y <;> cases hy0 : f false <;> cases hy1 : f true <;>
    simp [deutschState, H1, H2, oracle, init, sgn, hy0, hy1] <;> ring

lemma hcoe_pow_six : hcoe ^ 6 = 1 / 8 := by
  calc hcoe ^ 6 = (hcoe ^ 2) ^ 3 := by ring
    _ = 1 / 8 := by rw [hcoe_sq]; norm_num

/-- Sanity check: the final state is a unit vector, i.e. the measurement probabilities
sum to one. -/
lemma total_probability (f : Bool → Bool) :
    ∑ z : Bool, ∑ y : Bool, ‖deutschState f z y‖ ^ 2 = 1 := by
  simp only [Fintype.sum_bool, deutschState_false, deutschState_true]
  cases hy0 : f false <;> cases hy1 : f true <;>
    simp [sgn, mul_pow, abs_of_nonneg hcoe_nonneg] <;>
      norm_num <;> nlinarith [hcoe_pow_six]

lemma norm_deutschState_false_sq (f : Bool → Bool) (y : Bool) :
    ‖deutschState f false y‖ ^ 2 = if f false = f true then 1 / 2 else 0 := by
  rw [deutschState_false]
  cases y <;> cases hy0 : f false <;> cases hy1 : f true <;>
    simp [sgn, norm_pow, mul_pow, abs_of_nonneg hcoe_nonneg] <;>
      norm_num <;> nlinarith [hcoe_pow_six]

lemma prob0_eq (f : Bool → Bool) : prob0 f = if f false = f true then 1 else 0 := by
  rw [prob0, norm_deutschState_false_sq, norm_deutschState_false_sq]
  split <;> norm_num

/-- **Deutsch's algorithm is correct.**  With a single query to the oracle for
`f : {0,1} → {0,1}`, the probability of measuring `0` in the query register is `1` precisely
when `f` is constant, and `0` precisely when `f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    (prob0 f = 1 ↔ IsConstant f) ∧ (prob0 f = 0 ↔ IsBalanced f) := by
  rw [prob0_eq]
  refine ⟨⟨fun h x y => ?_, fun h => if_pos (h false true)⟩, ⟨fun h => ?_, fun h => if_neg h⟩⟩
  · by_cases hc : f false = f true
    · cases x <;> cases y <;> simp [hc]
    · rw [if_neg hc] at h; norm_num at h
  · by_cases hc : f false = f true
    · rw [if_pos hc] at h; norm_num at h
    · exact hc

end QC

