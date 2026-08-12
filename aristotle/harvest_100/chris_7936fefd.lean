import Mathlib

/-!
# Deutsch's algorithm

We formalise Deutsch's algorithm for a function `f : Bool → Bool` on one bit.

The two-qubit state space is modelled by amplitude functions `Bool → Bool → ℂ`
(the first argument is the "query" qubit, the second the "answer" qubit).

The circuit is

  |0⟩|1⟩  →  (H ⊗ H)  →  U_f  →  (H ⊗ I)  →  measure the first qubit,

where the oracle `U_f |x,y⟩ = |x, y ⊕ f x⟩` is applied **exactly once**
(the definition `QC.deutschFinal` contains a single occurrence of `QC.oracle f`,
and `f` occurs nowhere else in the circuit).

The main result `QC.deutsch_correct` states that measuring the first qubit
returns `false` with probability `1` iff `f` is constant, and `true` with
probability `1` iff `f` is balanced (`f false ≠ f true`).
-/

namespace QC

open Complex

/-- The scalar `1/√2` used by the Hadamard gate. -/
noncomputable def isqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- The sign `(-1)^b`. -/
def sign (b : Bool) : ℂ := if b then -1 else 1

/-- Hadamard gate acting on the first qubit. -/
noncomputable def hFirst (psi : Bool → Bool → ℂ) : Bool → Bool → ℂ :=
  fun x y => isqrt2 * (psi false y + sign x * psi true y)

/-- Hadamard gate acting on the second qubit. -/
noncomputable def hSecond (psi : Bool → Bool → ℂ) : Bool → Bool → ℂ :=
  fun x y => isqrt2 * (psi x false + sign y * psi x true)

/-- The oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`, acting on amplitudes. -/
def oracle (f : Bool → Bool) (psi : Bool → Bool → ℂ) : Bool → Bool → ℂ :=
  fun x y => psi x (xor y (f x))

/-- The initial state `|0⟩|1⟩`. -/
def initState : Bool → Bool → ℂ :=
  fun x y => if x = false ∧ y = true then 1 else 0

/-- The state at the end of Deutsch's circuit.  The oracle is queried once. -/
noncomputable def deutschFinal (f : Bool → Bool) : Bool → Bool → ℂ :=
  hFirst (oracle f (hSecond (hFirst initState)))

/-- Probability of observing the outcome `b` when measuring the first qubit
of the final state. -/
noncomputable def deutschProb (f : Bool → Bool) (b : Bool) : ℝ :=
  ‖deutschFinal f b false‖ ^ 2 + ‖deutschFinal f b true‖ ^ 2

lemma isqrt2_mul_isqrt2 : isqrt2 * isqrt2 = 1 / 2 := by
  have h : ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
    rw [← mul_inv]
    rw [Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [isqrt2, ← Complex.ofReal_mul, h]
  norm_num

lemma norm_isqrt2_sq : ‖isqrt2‖ ^ 2 = 1 / 2 := by
  have h : ‖isqrt2‖ = ((Real.sqrt 2)⁻¹ : ℝ) := by
    simp [isqrt2, abs_of_nonneg, Real.sqrt_nonneg]
  rw [h]
  rw [← Real.sqrt_inv, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Closed form for the amplitudes of the final state. -/
lemma deutschFinal_eq (f : Bool → Bool) (x y : Bool) :
    deutschFinal f x y =
      isqrt2 * (1 / 2) * sign y * (sign (f false) + sign x * sign (f true)) := by
  simp only [deutschFinal, hFirst, hSecond, oracle, initState, sign]
  cases x <;> cases y <;> cases hf : f false <;> cases ht : f true <;>
    simp [isqrt2_mul_isqrt2] <;> ring_nf

/-- **Deutsch's algorithm is correct.**  With a single query to the oracle
`U_f`, measuring the first qubit of the final state yields `false` with
probability `1` when `f` is constant, and `true` with probability `1` when `f`
is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    (f false = f true → deutschProb f false = 1 ∧ deutschProb f true = 0) ∧
    (f false ≠ f true → deutschProb f true = 1 ∧ deutschProb f false = 0) := by
  constructor <;> intro h <;>
    constructor <;>
    · simp only [deutschProb, deutschFinal_eq, sign]
      cases hf : f false <;> cases ht : f true <;>
        simp_all [norm_isqrt2_sq, mul_pow] <;> ring_nf <;> norm_num

/-- The two measurement outcomes have total probability `1`. -/
theorem deutschProb_add (f : Bool → Bool) :
    deutschProb f false + deutschProb f true = 1 := by
  by_cases h : f false = f true
  · obtain ⟨h1, h2⟩ := (deutsch_correct f).1 h
    rw [h1, h2]; norm_num
  · obtain ⟨h1, h2⟩ := (deutsch_correct f).2 h
    rw [h1, h2]; norm_num

/-- Measuring `false` happens with probability one exactly when `f` is constant. -/
theorem deutschProb_false_eq_one_iff (f : Bool → Bool) :
    deutschProb f false = 1 ↔ f false = f true := by
  constructor
  · intro h
    by_contra hne
    rw [((deutsch_correct f).2 hne).2] at h
    norm_num at h
  · intro h
    exact ((deutsch_correct f).1 h).1

/-- Measuring `true` happens with probability one exactly when `f` is balanced. -/
theorem deutschProb_true_eq_one_iff (f : Bool → Bool) :
    deutschProb f true = 1 ↔ f false ≠ f true := by
  constructor
  · intro h hc
    rw [((deutsch_correct f).1 hc).2] at h
    norm_num at h
  · intro h
    exact ((deutsch_correct f).2 h).1

end QC

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

