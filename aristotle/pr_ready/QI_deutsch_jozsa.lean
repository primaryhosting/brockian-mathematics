/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

/-- The phase `(-1)^(x ⬝ y)` coming from the final layer of Hadamard gates,
written as the product of the bitwise contributions. -/
def phase {n : ℕ} (x y : Fin n → Bool) : ℝ := ∏ i, (if x i && y i then (-1 : ℝ) else 1)

/-- The amplitude of the basis state `y` in the final state of the Deutsch–Jozsa
circuit `H^{⊗n} ∘ O_f ∘ H^{⊗n}` applied to `|0…0⟩`, where the oracle `O_f` (used
exactly once) contributes the phase `(-1)^{f x}`. -/
noncomputable def amp {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) : ℝ :=
  (1 / 2 ^ n) * ∑ x, sign (f x) * phase x y

/-- `f` is constant. -/
def IsConstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: exactly half of the inputs are mapped to `true`. -/
def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  2 * (univ.filter fun x => f x = true).card = 2 ^ n

/-- The all-zeros bit string, i.e. the outcome the algorithm looks for. -/
def zeroStr (n : ℕ) : Fin n → Bool := fun _ => false

lemma phase_zero {n : ℕ} (x : Fin n → Bool) : phase x (zeroStr n) = 1 := by
  simp [phase, zeroStr]

lemma card_true_add_card_false {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (univ.filter fun x => f x = true).card + (univ.filter fun x => f x = false).card = 2 ^ n := by
  classical
  have h : (univ.filter fun x : Fin n → Bool => f x = false)
      = univ.filter fun x => ¬ (f x = true) := by
    apply Finset.filter_congr
    intro x _
    cases hx : f x <;> simp_all
  rw [h, Finset.card_filter_add_card_filter_not]
  simp

/-- The key sum: `∑_x (-1)^{f x} = #{f = false} - #{f = true}`. -/
lemma sum_sign {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ x, sign (f x)
      = ((univ.filter fun x => f x = false).card : ℝ)
        - ((univ.filter fun x => f x = true).card : ℝ) := by
  classical
  have : ∑ x, sign (f x)
      = (∑ x ∈ univ.filter fun x => f x = true, sign (f x))
        + ∑ x ∈ univ.filter fun x => ¬ (f x = true), sign (f x) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [this]
  have h1 : (∑ x ∈ univ.filter fun x : Fin n → Bool => f x = true, sign (f x))
      = -((univ.filter fun x => f x = true).card : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℝ))]
    · simp
    · intro x hx
      simp only [Finset.mem_filter] at hx
      simp [sign, hx.2]
  have h2 : (∑ x ∈ univ.filter fun x : Fin n → Bool => ¬ (f x = true), sign (f x))
      = ((univ.filter fun x => f x = false).card : ℝ) := by
    have hset : (univ.filter fun x : Fin n → Bool => ¬ (f x = true))
        = univ.filter fun x => f x = false := by
      apply Finset.filter_congr
      intro x _
      cases hx : f x <;> simp_all
    rw [hset, Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp
    · intro x hx
      simp only [Finset.mem_filter] at hx
      simp [sign, hx.2]
  rw [h1, h2]; ring

lemma amp_zeroStr {n : ℕ} (f : (Fin n → Bool) → Bool) :
    amp f (zeroStr n) = (1 / 2 ^ n) *
      (((univ.filter fun x => f x = false).card : ℝ)
        - ((univ.filter fun x => f x = true).card : ℝ)) := by
  unfold amp
  rw [← sum_sign]
  simp [phase_zero]

/-- **Balanced case**: the amplitude of the all-zeros outcome vanishes. -/
theorem amp_eq_zero_of_balanced {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsBalanced f) :
    amp f (zeroStr n) = 0 := by
  have hc := card_true_add_card_false f
  unfold IsBalanced at h
  have : (univ.filter fun x : Fin n → Bool => f x = false).card
      = (univ.filter fun x => f x = true).card := by omega
  rw [amp_zeroStr, this]
  simp

/-- Conversely, a vanishing amplitude forces the function to be balanced. -/
theorem balanced_of_amp_eq_zero {n : ℕ} (f : (Fin n → Bool) → Bool)
    (h : amp f (zeroStr n) = 0) : IsBalanced f := by
  rw [amp_zeroStr] at h
  have hpow : (1 / 2 ^ n : ℝ) ≠ 0 := by positivity
  have h2 : ((univ.filter fun x : Fin n → Bool => f x = false).card : ℝ)
      - ((univ.filter fun x => f x = true).card : ℝ) = 0 := by
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hpow
    · exact h'
  have h3 : (univ.filter fun x : Fin n → Bool => f x = false).card
      = (univ.filter fun x => f x = true).card := by
    have := sub_eq_zero.1 h2
    exact_mod_cast this
  have hc := card_true_add_card_false f
  unfold IsBalanced
  omega

/-- **Constant case**: the all-zeros outcome occurs with probability one. -/
theorem abs_amp_eq_one_of_constant {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsConstant f) :
    |amp f (zeroStr n)| = 1 := by
  classical
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  by_cases hcase : ∃ x, f x = true
  · obtain ⟨x0, hx0⟩ := hcase
    have hall : ∀ x, f x = true := fun x => (h x x0).trans hx0
    have h1 : (univ.filter fun x : Fin n → Bool => f x = true) = univ := by
      apply Finset.filter_true_of_mem; intro x _; exact hall x
    have h2 : (univ.filter fun x : Fin n → Bool => f x = false) = ∅ := by
      apply Finset.filter_false_of_mem; intro x _; simp [hall x]
    have hval : amp f (zeroStr n) = -1 := by
      rw [amp_zeroStr, h1, h2]
      have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by simp
      simp only [Finset.card_empty, Nat.cast_zero, zero_sub, hcard]
      field_simp
    rw [hval]
    norm_num
  · push_neg at hcase
    have hall : ∀ x, f x = false := by
      intro x; cases hx : f x
      · rfl
      · exact absurd hx (hcase x)
    have h1 : (univ.filter fun x : Fin n → Bool => f x = true) = ∅ := by
      apply Finset.filter_false_of_mem; intro x _; simp [hall x]
    have h2 : (univ.filter fun x : Fin n → Bool => f x = false) = univ := by
      apply Finset.filter_true_of_mem; intro x _; exact hall x
    have hval : amp f (zeroStr n) = 1 := by
      rw [amp_zeroStr, h1, h2]
      have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by simp
      simp only [Finset.card_empty, Nat.cast_zero, sub_zero, hcard]
      field_simp
    rw [hval]
    norm_num

/-- **Deutsch–Jozsa.**  For a promise function `f : {0,1}^n → {0,1}` which is either
constant or balanced, one run of the circuit `H^{⊗n} ∘ O_f ∘ H^{⊗n}|0…0⟩` — which uses
the oracle `O_f` exactly once — decides which:  the all-zeros outcome has probability
`1` exactly when `f` is constant, and probability `0` exactly when `f` is balanced. -/
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool)
    (h : IsConstant f ∨ IsBalanced f) :
    (IsConstant f ↔ |amp f (zeroStr n)| = 1) ∧ (IsBalanced f ↔ amp f (zeroStr n) = 0) := by
  refine ⟨⟨abs_amp_eq_one_of_constant f, ?_⟩,
    ⟨amp_eq_zero_of_balanced f, balanced_of_amp_eq_zero f⟩⟩
  intro habs
  rcases h with hc | hb
  · exact hc
  · rw [amp_eq_zero_of_balanced f hb] at habs
    norm_num at habs

/-! ### Unitarity: the numbers `amp f y` really are the amplitudes of a quantum state -/

/-- Orthogonality of the rows of the `n`-fold Hadamard transform. -/
theorem phase_orthogonality {n : ℕ} (x x' : Fin n → Bool) :
    ∑ y, phase x y * phase x' y = if x = x' then (2 : ℝ) ^ n else 0 := by
  have key : ∀ y : Fin n → Bool, phase x y * phase x' y
      = ∏ i, ((if x i && y i then (-1 : ℝ) else 1) * (if x' i && y i then (-1 : ℝ) else 1)) := by
    intro y; rw [phase, phase, ← Finset.prod_mul_distrib]
  simp_rw [key]
  rw [show (∑ y : Fin n → Bool, ∏ i,
        ((if x i && y i then (-1 : ℝ) else 1) * (if x' i && y i then (-1 : ℝ) else 1)))
      = ∏ i, ∑ b : Bool,
        ((if x i && b then (-1 : ℝ) else 1) * (if x' i && b then (-1 : ℝ) else 1)) by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]]
  have hb : ∀ i, (∑ b : Bool,
      ((if x i && b then (-1 : ℝ) else 1) * (if x' i && b then (-1 : ℝ) else 1)))
      = if x i = x' i then (2 : ℝ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hx : x i <;> cases hx' : x' i <;> norm_num
  simp_rw [hb]
  by_cases h : x = x'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])

lemma sign_sq_eq_one (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]

/-- The final state of the circuit is a unit vector: the outcome probabilities
`(amp f y) ^ 2` sum to `1`. -/
theorem sum_amp_sq {n : ℕ} (f : (Fin n → Bool) → Bool) : ∑ y, (amp f y) ^ 2 = 1 := by
  have hsq : ∀ y : Fin n → Bool, (amp f y) ^ 2
      = (1 / 2 ^ n : ℝ) ^ 2 * ∑ x, ∑ x', (sign (f x) * sign (f x')) * (phase x y * phase x' y) := by
    intro y
    unfold amp
    rw [mul_pow]
    congr 1
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
  simp_rw [hsq]
  rw [← Finset.mul_sum]
  have hswap : (∑ y : Fin n → Bool, ∑ x, ∑ x',
        (sign (f x) * sign (f x')) * (phase x y * phase x' y))
      = ∑ x, ∑ x', (sign (f x) * sign (f x')) * ∑ y, (phase x y * phase x' y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x' _ => by rw [Finset.mul_sum]
  rw [hswap]
  simp_rw [phase_orthogonality, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    sign_sq_eq_one, one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
  rw [hc]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

end QI


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

