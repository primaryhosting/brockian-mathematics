import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

/-! ## Setup

We model the Deutsch–Jozsa algorithm on `n` query bits.  A computational basis
state is an element of `Fin n → Bool`, and a (pure) state of the query register
is a function `(Fin n → Bool) → ℂ` of amplitudes. -/

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/
noncomputable def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- The uniform superposition over all `2^n` basis states. -/
noncomputable def uniform (n : ℕ) : (Fin n → Bool) → ℂ :=
  fun _ => 1 / (Real.sqrt (2 ^ n) : ℝ)

/-- The `n`-fold Hadamard transform:
`H^{⊗n} ψ (y) = 2^{-n/2} ∑ₓ (-1)^{⟨x,y⟩} ψ x`, where the sign `(-1)^{⟨x,y⟩}` is
written as the product `∏ᵢ (-1)^{xᵢ ∧ yᵢ}`. -/
noncomputable def hadamard (psi : (Fin n → Bool) → ℂ) : (Fin n → Bool) → ℂ :=
  fun y => (1 / (Real.sqrt (2 ^ n) : ℝ)) * ∑ x : Fin n → Bool, (∏ i, sgn (x i && y i)) * psi x

/-- The state of the query register after the phase oracle for `f` has acted on
the uniform superposition. -/
noncomputable def phaseOracleState (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℂ :=
  fun x => sgn (f x) * uniform n x

/-- The final state of the Deutsch–Jozsa algorithm: uniform superposition, one
oracle query, then a Hadamard transform. -/
noncomputable def djFinal (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℂ :=
  hadamard (phaseOracleState f)

/-- The all-zero basis state. -/
def zeroState (n : ℕ) : Fin n → Bool := fun _ => false

/-- The probability that the final measurement returns the all-zero string. -/
noncomputable def djZeroProb (f : (Fin n → Bool) → Bool) : ℝ :=
  ‖djFinal f (zeroState n)‖ ^ 2

/-- `f` is constant. -/
def IsConstant (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: exactly half of the inputs are mapped to `true`. -/
def IsBalanced (f : (Fin n → Bool) → Bool) : Prop :=
  2 * (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card = 2 ^ n

/-! ## The standard XOR oracle and phase kickback -/

/-- The standard oracle `U_f |x, b⟩ = |x, b ⊕ f x⟩`, acting on amplitudes. -/
noncomputable def xorOracle (f : (Fin n → Bool) → Bool)
    (psi : (Fin n → Bool) × Bool → ℂ) : (Fin n → Bool) × Bool → ℂ :=
  fun p => psi (p.1, xor p.2 (f p.1))

/-- The `|−⟩` state of the answer qubit. -/
noncomputable def minusState : Bool → ℂ := fun b => sgn b * (1 / (Real.sqrt 2 : ℝ))

/-- Phase kickback: the standard XOR oracle acting on `|uniform⟩ ⊗ |−⟩` produces
the phase-oracle state tensored with `|−⟩`.  This justifies using
`phaseOracleState` as the state after a single query. -/
theorem phase_kickback (f : (Fin n → Bool) → Bool) :
    xorOracle f (fun p => uniform n p.1 * minusState p.2)
      = fun p => phaseOracleState f p.1 * minusState p.2 := by
  funext p
  obtain ⟨x, b⟩ := p
  cases b <;> cases hfx : f x <;>
    simp [xorOracle, minusState, phaseOracleState, sgn, hfx]

/-! ## Auxiliary lemmas -/

theorem sqrt_two_pow_sq (n : ℕ) :
    ((Real.sqrt (2 ^ n) : ℝ) : ℂ) * ((Real.sqrt (2 ^ n) : ℝ) : ℂ) = (2 : ℂ) ^ n := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- The sum of the query phases equals `2^n - 2 · #{x | f x}`. -/
theorem sum_sgn (f : (Fin n → Bool) → Bool) :
    (∑ x : Fin n → Bool, sgn (f x))
      = (2 : ℂ) ^ n - 2 * ((Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card : ℂ) := by
  have h : ∀ x : Fin n → Bool, sgn (f x) = 1 - 2 * (if f x = true then (1 : ℂ) else 0) := by
    intro x
    simp only [sgn]
    split <;> norm_num
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_boole]
  simp [Finset.card_univ]

/-- The amplitude of the all-zero outcome after one query. -/
theorem djFinal_zero (f : (Fin n → Bool) → Bool) :
    djFinal f (zeroState n) = (1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, sgn (f x) := by
  have h2 : (1 / ((Real.sqrt (2 ^ n) : ℝ) : ℂ)) * (1 / ((Real.sqrt (2 ^ n) : ℝ) : ℂ))
      = 1 / (2 : ℂ) ^ n := by
    rw [div_mul_div_comm, sqrt_two_pow_sq]
    norm_num
  simp only [djFinal, hadamard, phaseOracleState, uniform, zeroState, Bool.and_false, sgn,
    Bool.false_eq_true, if_false, Finset.prod_const_one, one_mul, ← Finset.sum_mul]
  linear_combination (∑ x : Fin n → Bool, (if f x = true then (-1 : ℂ) else 1)) * h2

theorem card_true_of_constant (f : (Fin n → Bool) → Bool) (hf : IsConstant f) :
    (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card = 0 ∨
    (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card = 2 ^ n := by
  by_cases h : f (fun _ => false) = true
  · right
    have huniv : (Finset.univ.filter (fun x : Fin n → Bool => f x = true)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro x _
      rw [hf x (fun _ => false)]
      exact h
    rw [huniv]
    simp
  · left
    rw [Finset.card_eq_zero]
    apply Finset.filter_false_of_mem
    intro x _
    rw [hf x (fun _ => false)]
    exact h

/-- A constant function and a balanced function are never the same function. -/
theorem not_constant_and_balanced (f : (Fin n → Bool) → Bool) :
    ¬ (IsConstant f ∧ IsBalanced f) := by
  rintro ⟨hc, hb⟩
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [IsBalanced] at hb
  rcases card_true_of_constant f hc with h | h <;> rw [h] at hb <;> omega

/-- For a constant `f`, the all-zero outcome has amplitude of modulus one. -/
theorem djFinal_zero_of_constant (f : (Fin n → Bool) → Bool) (hf : IsConstant f) :
    ‖djFinal f (zeroState n)‖ = 1 := by
  have hne : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  rw [djFinal_zero, sum_sgn]
  rcases card_true_of_constant f hf with h | h <;> rw [h]
  · rw [Nat.cast_zero, mul_zero, sub_zero, one_div, inv_mul_cancel₀ hne, norm_one]
  · push_cast
    rw [show (1 / (2 : ℂ) ^ n) * ((2 : ℂ) ^ n - 2 * (2 : ℂ) ^ n) = -1 by field_simp; norm_num]
    norm_num

/-- For a balanced `f`, the all-zero outcome has amplitude zero. -/
theorem djFinal_zero_of_balanced (f : (Fin n → Bool) → Bool) (hf : IsBalanced f) :
    djFinal f (zeroState n) = 0 := by
  rw [djFinal_zero, sum_sgn]
  have : ((2 * (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card : ℕ) : ℂ)
      = ((2 ^ n : ℕ) : ℂ) := by
    rw [hf]
  push_cast at this
  rw [← this]
  ring

/-! ## Main theorem -/

/-- **Deutsch–Jozsa.**  Given the promise that `f : (Fin n → Bool) → Bool` is
either constant or balanced, a single query to the oracle suffices to decide
which: after one query and a Hadamard transform, the all-zero measurement
outcome occurs with probability `1` exactly when `f` is constant, and with
probability `0` exactly when `f` is balanced. -/
theorem deutsch_jozsa (f : (Fin n → Bool) → Bool) (hf : IsConstant f ∨ IsBalanced f) :
    (djZeroProb f = 1 ↔ IsConstant f) ∧ (djZeroProb f = 0 ↔ IsBalanced f) := by
  have hconst : IsConstant f → djZeroProb f = 1 := by
    intro hc
    rw [djZeroProb, djFinal_zero_of_constant f hc, one_pow]
  have hbal : IsBalanced f → djZeroProb f = 0 := by
    intro hb
    rw [djZeroProb, djFinal_zero_of_balanced f hb]
    norm_num
  refine ⟨⟨fun h => ?_, hconst⟩, ⟨fun h => ?_, hbal⟩⟩
  · rcases hf with hc | hb
    · exact hc
    · rw [hbal hb] at h
      norm_num at h
  · rcases hf with hc | hb
    · rw [hconst hc] at h
      norm_num at h
    · exact hb

end QI

