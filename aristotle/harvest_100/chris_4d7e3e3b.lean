/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

open Finset

/-- The number of inputs `x` on which the oracle `f` returns `true`. -/
noncomputable def numTrue {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (univ.filter (fun x => f x = true)).card

/-- `f` is constant. -/
def IsConstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: it returns `true` on exactly half of its `2 ^ n` inputs. -/
def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := 2 * numTrue f = 2 ^ n

/-- The amplitude of the all-zeros basis state measured at the end of the
Deutsch–Jozsa circuit, after a *single* query to the phase oracle for `f`:
`2⁻ⁿ ∑ₓ (-1)^{f(x)}`. -/
noncomputable def amplitude {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (1 / 2 ^ n) * ∑ x : Fin n → Bool, (if f x then (-1 : ℝ) else 1)

lemma sum_sign {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ x : Fin n → Bool, (if f x then (-1 : ℝ) else 1)
      = (2 ^ n : ℝ) - 2 * (numTrue f : ℝ) := by
  have hcast : ∀ x : Fin n → Bool,
      (if f x then (-1 : ℝ) else 1) = 1 - 2 * (if f x = true then (1 : ℝ) else 0) := by
    intro x; cases hx : f x <;> norm_num
  rw [Finset.sum_congr rfl fun x _ => hcast x, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Finset.card_univ]
  simp [hcard, numTrue]

lemma amplitude_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    amplitude f = 1 - 2 * (numTrue f : ℝ) / 2 ^ n := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [amplitude, sum_sign]
  field_simp

/-- Sign `(-1)^{x·y}` of the bitwise inner product of two `n`-bit strings. -/
noncomputable def dotSign {n : ℕ} (x y : Fin n → Bool) : ℝ :=
  if Odd ((univ.filter (fun i => x i && y i = true)).card) then -1 else 1

/-- The `n`-fold Hadamard transform `H^{⊗n}` acting on a real amplitude vector. -/
noncomputable def hadamardAll {n : ℕ} (psi : (Fin n → Bool) → ℝ) : (Fin n → Bool) → ℝ :=
  fun y => ((Real.sqrt 2) ^ n)⁻¹ * ∑ x : Fin n → Bool, dotSign x y * psi x

/-- The all-zeros computational basis state `|0…0⟩`. -/
noncomputable def zeroState {n : ℕ} : (Fin n → Bool) → ℝ :=
  fun x => if x = (fun _ => false) then 1 else 0

/-- The phase oracle `|x⟩ ↦ (-1)^{f(x)} |x⟩`: this is the *single* query to `f`. -/
noncomputable def oraclePhase {n : ℕ} (f : (Fin n → Bool) → Bool)
    (psi : (Fin n → Bool) → ℝ) : (Fin n → Bool) → ℝ :=
  fun x => (if f x then (-1 : ℝ) else 1) * psi x

/-- The Deutsch–Jozsa circuit: start in `|0…0⟩`, apply `H^{⊗n}`, query the phase
oracle for `f` once, apply `H^{⊗n}` again. -/
noncomputable def djOutput {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℝ :=
  hadamardAll (oraclePhase f (hadamardAll zeroState))

lemma dotSign_zero_right {n : ℕ} (x : Fin n → Bool) : dotSign x (fun _ => false) = 1 := by
  simp [dotSign]

lemma dotSign_zero_left {n : ℕ} (y : Fin n → Bool) : dotSign (fun _ => false) y = 1 := by
  simp [dotSign]

/-- After the first Hadamard layer the register is in the uniform superposition. -/
lemma hadamardAll_zeroState {n : ℕ} :
    hadamardAll (zeroState : (Fin n → Bool) → ℝ) = fun _ => ((Real.sqrt 2) ^ n)⁻¹ := by
  funext y
  simp [hadamardAll, zeroState, Finset.sum_ite_eq', dotSign_zero_left]

/-- The amplitude the circuit assigns to the all-zeros outcome is exactly
`2⁻ⁿ ∑ₓ (-1)^{f(x)}`. -/
lemma djOutput_zero {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djOutput f (fun _ => false) = amplitude f := by
  have hc : ((Real.sqrt 2) ^ n)⁻¹ * ((Real.sqrt 2) ^ n)⁻¹ = (1 / 2 ^ n : ℝ) := by
    rw [← mul_inv, ← mul_pow, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2), one_div]
  unfold djOutput
  rw [hadamardAll_zeroState]
  simp only [hadamardAll, oraclePhase, dotSign_zero_right, one_mul, amplitude,
    ← Finset.sum_mul, ← mul_assoc]
  rw [mul_right_comm, hc]

/-- **Deutsch–Jozsa.** With a single query to the oracle for `f`, the amplitude
`2⁻ⁿ ∑ₓ (-1)^{f(x)}` of the all-zeros outcome distinguishes the two promises:
it has modulus `1` when `f` is constant (the all-zeros outcome occurs with
probability one) and is `0` when `f` is balanced (the all-zeros outcome never
occurs). Hence one measurement decides constant vs. balanced. -/
theorem deutsch_jozsa_amplitude {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (IsConstant f → |amplitude f| = 1) ∧ (IsBalanced f → amplitude f = 0) := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  constructor
  · intro hconst
    by_cases hex : ∃ x : Fin n → Bool, f x = true
    · obtain ⟨x0, hx0⟩ := hex
      have hall : ∀ x : Fin n → Bool, f x = true := fun x => (hconst x x0).trans hx0
      have hnum : numTrue f = 2 ^ n := by
        unfold numTrue
        rw [Finset.filter_true_of_mem (fun x _ => hall x)]
        simp [Finset.card_univ]
      rw [amplitude_eq, hnum]
      push_cast
      rw [show (1 : ℝ) - 2 * 2 ^ n / 2 ^ n = -1 by field_simp; norm_num]
      simp
    · push_neg at hex
      have hnum : numTrue f = 0 := by
        unfold numTrue
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _
        simp [hex x]
      rw [amplitude_eq, hnum]
      norm_num
  · intro hbal
    have hnum : 2 * (numTrue f : ℝ) = 2 ^ n := by
      have := congrArg (fun k : ℕ => (k : ℝ)) hbal
      push_cast at this
      exact this
    rw [amplitude_eq, hnum]
    field_simp
    norm_num

/-- **Deutsch–Jozsa.** Running the circuit `H^{⊗n} ∘ Uf ∘ H^{⊗n}` on `|0…0⟩`,
with a *single* query to the oracle for `f`, the amplitude of the all-zeros
measurement outcome has modulus `1` when `f` is constant (so that outcome is
observed with probability one) and is `0` when `f` is balanced (so that outcome
is never observed).  Hence one query and one measurement decide constant vs.
balanced. -/
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (IsConstant f → |djOutput f (fun _ => false)| = 1) ∧
      (IsBalanced f → djOutput f (fun _ => false) = 0) := by
  rw [djOutput_zero]
  exact deutsch_jozsa_amplitude f

end QI

