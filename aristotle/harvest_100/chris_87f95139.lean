/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-- The number of inputs on which `f` takes the value `true`. -/
def trueCount {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

/-- `f` is constant. -/
def IsConstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: exactly half of the `2 ^ n` inputs are mapped to `true`. -/
def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := 2 * trueCount f = 2 ^ n

/-- The mod-2 inner product `x · y` of two bit strings, as a natural number. -/
def parityDot {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => (x i && y i) = true).card

/-- The amplitude of the basis state `y` in the final state of the Deutsch–Jozsa
circuit: apply Hadamards, one phase query to `f`, and Hadamards again. -/
noncomputable def djAmp {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) : ℝ :=
  (∑ x : Fin n → Bool, (-1 : ℝ) ^ ((f x).toNat + parityDot x y)) / 2 ^ n

/-- The probability of observing the all-zeros string. -/
noncomputable def djZeroProb {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (djAmp f (fun _ => false)) ^ 2

lemma card_domain (n : ℕ) : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  simp

lemma trueCount_le {n : ℕ} (f : (Fin n → Bool) → Bool) : trueCount f ≤ 2 ^ n := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin n → Bool)) (fun x => f x = true)
  simpa [trueCount, card_domain] using this

lemma parityDot_zero {n : ℕ} (x : Fin n → Bool) : parityDot x (fun _ => false) = 0 := by
  simp [parityDot]

/-- Explicit value of the all-zeros amplitude in terms of the number of `true` inputs. -/
lemma djAmp_zero_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f (fun _ => false) = ((2 ^ n : ℝ) - 2 * trueCount f) / 2 ^ n := by
  have hsum : (∑ x : Fin n → Bool, (-1 : ℝ) ^ ((f x).toNat + parityDot x (fun _ => false)))
      = (2 ^ n : ℝ) - 2 * trueCount f := by
    have h1 : ∀ x : Fin n → Bool,
        (-1 : ℝ) ^ ((f x).toNat + parityDot x (fun _ => false))
          = if f x = true then (-1 : ℝ) else 1 := by
      intro x
      rcases hx : f x with _ | _ <;> simp [parityDot_zero]
    rw [Finset.sum_congr rfl (fun x _ => h1 x)]
    rw [Finset.sum_ite]
    have hT : (Finset.univ.filter fun x : Fin n → Bool => f x = true).card = trueCount f := rfl
    have hF : (Finset.univ.filter fun x : Fin n → Bool => ¬ (f x = true)).card
        = 2 ^ n - trueCount f := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Bool))) (p := fun x => f x = true)
      rw [card_domain] at this
      omega
    have hle : trueCount f ≤ 2 ^ n := trueCount_le f
    simp only [Finset.sum_const, nsmul_eq_mul, hT, hF]
    have : ((2 ^ n - trueCount f : ℕ) : ℝ) = (2 ^ n : ℝ) - trueCount f := by
      push_cast [Nat.cast_sub hle]
      ring
    rw [this]
    ring
  rw [djAmp, hsum]

lemma isConstant_iff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsConstant f ↔ trueCount f = 0 ∨ trueCount f = 2 ^ n := by
  constructor
  · intro h
    by_cases hx : ∃ x, f x = true
    · obtain ⟨x, hxt⟩ := hx
      right
      have : ∀ y : Fin n → Bool, f y = true := fun y => (h y x).trans hxt
      simp [trueCount, this]
    · left
      push_neg at hx
      simp [trueCount, hx]
  · intro h
    rcases h with h | h
    · have : ∀ x : Fin n → Bool, f x ≠ true := by
        intro x hx
        have hmem : x ∈ (Finset.univ.filter fun x => f x = true) := by simp [hx]
        rw [Finset.card_eq_zero.mp h] at hmem
        simp at hmem
      intro x y
      simp [Bool.eq_false_iff.mpr (this x), Bool.eq_false_iff.mpr (this y)]
    · have hall : (Finset.univ.filter fun x : Fin n → Bool => f x = true) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [← card_domain n] at h
        exact h
      intro x y
      have hx : f x = true := by
        have : x ∈ (Finset.univ.filter fun x : Fin n → Bool => f x = true) := by
          rw [hall]; exact Finset.mem_univ x
        simpa using this
      have hy : f y = true := by
        have : y ∈ (Finset.univ.filter fun x : Fin n → Bool => f x = true) := by
          rw [hall]; exact Finset.mem_univ y
        simpa using this
      rw [hx, hy]

/-- **Deutsch–Jozsa.** A single query to the phase oracle for `f` suffices to decide
whether `f` is constant or balanced: the amplitude of the all-zeros outcome has
modulus `1` exactly when `f` is constant, and vanishes exactly when `f` is balanced.
Consequently, under the promise that `f` is constant or balanced, the outcome of the
single measurement determines which case holds. -/
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (IsConstant f ↔ |djAmp f (fun _ => false)| = 1) ∧
    (IsBalanced f ↔ djAmp f (fun _ => false) = 0) ∧
    ((IsConstant f ∨ IsBalanced f) →
      ((djZeroProb f = 1 ∧ IsConstant f) ∨ (djZeroProb f = 0 ∧ IsBalanced f))) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hle : trueCount f ≤ 2 ^ n := trueCount_le f
  have hT : ((trueCount f : ℝ)) ≤ (2 ^ n : ℝ) := by exact_mod_cast hle
  have hval := djAmp_zero_eq f
  have hconst : IsConstant f ↔ |djAmp f (fun _ => false)| = 1 := by
    rw [hval, isConstant_iff]
    rw [abs_div, abs_of_pos hpow, div_eq_one_iff_eq (ne_of_gt hpow)]
    constructor
    · rintro (h | h) <;> rw [h] <;> push_cast
      · rw [mul_zero, sub_zero, abs_of_pos hpow]
      · rw [show (2:ℝ) ^ n - 2 * 2 ^ n = -(2 ^ n) by ring, abs_neg, abs_of_pos hpow]
    · intro h
      rcases abs_eq (le_of_lt hpow) |>.mp h with h' | h'
      · left
        have : (trueCount f : ℝ) = 0 := by linarith
        exact_mod_cast this
      · right
        have : (trueCount f : ℝ) = (2 ^ n : ℝ) := by linarith
        exact_mod_cast this
  have hbal : IsBalanced f ↔ djAmp f (fun _ => false) = 0 := by
    rw [hval, div_eq_zero_iff]
    constructor
    · intro h
      left
      have h' : ((2 * trueCount f : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    · rintro (h | h)
      · have : (2 : ℝ) * trueCount f = 2 ^ n := by linarith
        have : ((2 * trueCount f : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      · exact absurd h (ne_of_gt hpow)
  refine ⟨hconst, hbal, ?_⟩
  rintro (h | h)
  · left
    refine ⟨?_, h⟩
    have habs := hconst.mp h
    rw [djZeroProb, ← sq_abs, habs, one_pow]
  · right
    exact ⟨by rw [djZeroProb, hbal.mp h]; ring, h⟩

end QI

