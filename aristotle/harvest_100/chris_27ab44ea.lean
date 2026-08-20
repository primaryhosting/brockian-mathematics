/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QI

open Finset

/-- The sign `(-1)^(f x)` attached to a Boolean value. -/
def sign (b : Bool) : ℚ := if b then -1 else 1

/-- Number of inputs on which `f` returns `true`. -/
def numTrue {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (univ.filter fun x => f x = true).card

/-- The amplitude of the all-zeros outcome after the Deutsch–Jozsa circuit
(one oracle query, Hadamards before and after):
`2⁻ⁿ ∑_x (-1)^(f x)`. -/
def djAmp {n : ℕ} (f : (Fin n → Bool) → Bool) : ℚ :=
  (∑ x : Fin n → Bool, sign (f x)) / 2 ^ n

/-- `f` is constant. -/
def IsConstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∃ b, ∀ x, f x = b

/-- `f` is balanced: it returns `true` on exactly half of its inputs. -/
def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := 2 * numTrue f = 2 ^ n

lemma card_domain (n : ℕ) : (univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  simp

lemma djSum_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (∑ x : Fin n → Bool, sign (f x)) = 2 ^ n - 2 * (numTrue f : ℚ) := by
  have h : ∀ x : Fin n → Bool, sign (f x) = 1 - 2 * (if f x = true then (1 : ℚ) else 0) := by
    intro x
    unfold sign
    cases f x <;> norm_num
  rw [Finset.sum_congr rfl fun x _ => h x]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [numTrue, card_domain]

lemma djAmp_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f = (2 ^ n - 2 * (numTrue f : ℚ)) / 2 ^ n := by
  rw [djAmp, djSum_eq]

lemma numTrue_eq_zero_iff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    numTrue f = 0 ↔ ∀ x, f x = false := by
  rw [numTrue, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x; simpa using h (Finset.mem_univ x)
  · intro h x _; simp [h x]

lemma numTrue_eq_card_iff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    numTrue f = 2 ^ n ↔ ∀ x, f x = true := by
  constructor
  · intro h
    have hsub : (univ.filter fun x => f x = true) = (univ : Finset (Fin n → Bool)) := by
      apply Finset.eq_univ_of_card
      simpa [numTrue] using h
    intro x
    have : x ∈ (univ.filter fun x => f x = true) := by rw [hsub]; exact Finset.mem_univ x
    simpa using this
  · intro h
    have : (univ.filter fun x => f x = true) = (univ : Finset (Fin n → Bool)) := by
      apply Finset.filter_true_of_mem
      intro x _; exact h x
    rw [numTrue, this, card_domain]

lemma numTrue_le {n : ℕ} (f : (Fin n → Bool) → Bool) : numTrue f ≤ 2 ^ n := by
  rw [numTrue, ← card_domain n]
  exact Finset.card_filter_le _ _

/-- **Deutsch–Jozsa.**  With a single oracle query, the amplitude of the all-zeros
measurement outcome distinguishes constant from balanced functions:
it has modulus `1` exactly when `f` is constant, and vanishes exactly when `f` is
balanced.  In particular the two cases are perfectly distinguished by one query. -/
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (|djAmp f| = 1 ↔ IsConstant f) ∧ (djAmp f = 0 ↔ IsBalanced f) := by
  have hpow : (0 : ℚ) < 2 ^ n := by positivity
  have hT : (numTrue f : ℚ) ≤ 2 ^ n := by
    exact_mod_cast numTrue_le f
  have hamp := djAmp_eq f
  constructor
  · rw [hamp, abs_div, abs_of_pos hpow, div_eq_one_iff_eq hpow.ne']
    constructor
    · intro h
      rcases abs_eq (le_of_lt hpow) |>.1 h with h1 | h1
      · -- 2^n - 2T = 2^n, so T = 0
        have : (numTrue f : ℚ) = 0 := by linarith
        have h0 : numTrue f = 0 := by exact_mod_cast this
        exact ⟨false, (numTrue_eq_zero_iff f).1 h0⟩
      · have : (numTrue f : ℚ) = 2 ^ n := by linarith
        have h0 : numTrue f = 2 ^ n := by exact_mod_cast this
        exact ⟨true, (numTrue_eq_card_iff f).1 h0⟩
    · rintro ⟨b, hb⟩
      cases b with
      | false =>
        have h0 : numTrue f = 0 := (numTrue_eq_zero_iff f).2 hb
        rw [h0]
        simp
      | true =>
        have h0 : numTrue f = 2 ^ n := (numTrue_eq_card_iff f).2 hb
        rw [h0]
        simp
  · rw [hamp, div_eq_zero_iff]
    constructor
    · intro h
      rcases h with h | h
      · have : (2 : ℚ) * numTrue f = 2 ^ n := by linarith
        have : ((2 * numTrue f : ℕ) : ℚ) = ((2 ^ n : ℕ) : ℚ) := by push_cast; linarith
        exact_mod_cast this
      · exact absurd h hpow.ne'
    · intro h
      left
      have : ((2 * numTrue f : ℕ) : ℚ) = ((2 ^ n : ℕ) : ℚ) := by exact_mod_cast congrArg _ h
      push_cast at this
      linarith

end QI

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

