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

/-
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Brockian
namespace WeirdNumbers

/-- `n` is *semiperfect* (pseudoperfect) if `n` is positive and some set of proper divisors
of `n` sums to `n`. -/
def Semiperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ∈ n.properDivisors.powerset, ∑ d ∈ S, d = n

instance (n : ℕ) : Decidable (Semiperfect n) := by
  unfold Semiperfect; infer_instance

/-- `n` is *weird* if it is abundant (the sum of its proper divisors exceeds `n`) but not
semiperfect. -/
def Weird (n : ℕ) : Prop := n.Abundant ∧ ¬ Semiperfect n

instance (n : ℕ) : Decidable (Weird n) := by
  unfold Weird; infer_instance

/-- The Brockian statement: **there exists an odd weird number**.  Whether this holds is a
well-known open problem; the results below are unconditional partial results about it. -/
def OddWeirdExists : Prop := ∃ n : ℕ, Odd n ∧ Weird n

/-! ## Basic facts -/

theorem Semiperfect.pos {n : ℕ} (h : Semiperfect n) : 0 < n := h.1

theorem semiperfect_def {n : ℕ} :
    Semiperfect n ↔ 0 < n ∧ ∃ S ⊆ n.properDivisors, ∑ d ∈ S, d = n := by
  simp [Semiperfect, Finset.mem_powerset]

theorem abundant_pos {n : ℕ} (h : n.Abundant) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.Abundant] at h
  · exact hn

theorem Weird.pos {n : ℕ} (h : Weird n) : 0 < n := abundant_pos h.1

/-! ## Multiples of semiperfect numbers are semiperfect -/

/-- Any positive multiple of a semiperfect number is semiperfect. -/
theorem semiperfect_of_dvd {m n : ℕ} (hn : 0 < n) (hmn : m ∣ n) (hm : Semiperfect m) :
    Semiperfect n := by
  obtain ⟨hm0, S, hS, hsum⟩ := semiperfect_def.1 hm
  obtain ⟨k, rfl⟩ := hmn
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hn
    · exact hk
  refine semiperfect_def.2 ⟨hn, S.image (fun d => d * k), ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨d, hd, rfl⟩ := ht
    have hd' := hS hd
    rw [Nat.mem_properDivisors] at hd' ⊢
    exact ⟨mul_dvd_mul_right hd'.1 k, Nat.mul_lt_mul_of_lt_of_le hd'.2 le_rfl hk⟩
  · rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hk hab),
      ← Finset.sum_mul, hsum]

/-- A weird number has no semiperfect divisor. -/
theorem Weird.no_semiperfect_divisor {n d : ℕ} (hn : Weird n) (hd : d ∣ n) :
    ¬ Semiperfect d := fun h => hn.2 (semiperfect_of_dvd hn.pos hd h)

/-! ## Weird numbers exist (70 is the smallest one) -/

theorem semiperfect_six : Semiperfect 6 := by decide

theorem weird_70 : Weird 70 := by decide

theorem weird_exists : ∃ n : ℕ, Weird n := ⟨70, weird_70⟩

/-! ## 945 is semiperfect, hence no weird number is divisible by 945 -/

theorem semiperfect_945 : Semiperfect 945 := by
  refine ⟨by norm_num, ({1, 5, 7, 9, 15, 21, 35, 45, 63, 105, 135, 189, 315} : Finset ℕ), ?_, ?_⟩
  · rw [Finset.mem_powerset]; decide
  · decide

/-- No weird number is divisible by `945` (the smallest odd abundant number, which is
semiperfect). -/
theorem Weird.not_dvd_945 {n : ℕ} (hn : Weird n) : ¬ (945 ∣ n) := fun h =>
  hn.no_semiperfect_divisor h semiperfect_945

/-- No weird number is divisible by `6` (indeed by any perfect number). -/
theorem Weird.not_dvd_six {n : ℕ} (hn : Weird n) : ¬ (6 ∣ n) := fun h =>
  hn.no_semiperfect_divisor h semiperfect_six

/-! ## Lower bound for odd weird numbers -/

/-- Every odd abundant number is at least `945` (a finite verification). -/
theorem odd_abundant_ge_945 {n : ℕ} (hodd : Odd n) (habund : n.Abundant) : 945 ≤ n := by
  have key : ∀ m < 945, Odd m → ¬ m.Abundant := by decide
  by_contra h
  push_neg at h
  exact key n h hodd habund

/-- Every odd weird number is at least `947`. -/
theorem odd_weird_ge_947 {n : ℕ} (hodd : Odd n) (hw : Weird n) : 947 ≤ n := by
  have h945 := odd_abundant_ge_945 hodd hw.1
  have hpar : n % 2 = 1 := Nat.odd_iff.1 hodd
  have hne : n ≠ 945 := by
    rintro rfl
    exact hw.not_dvd_945 dvd_rfl
  omega

/-! ## Conditional reduction for the Brockian statement -/

/-- **Reduction.**  If an odd weird number exists at all, then there is one that is at least
`947`, is not divisible by `945`, and none of whose divisors is semiperfect. -/
theorem oddWeirdExists_iff :
    OddWeirdExists ↔
      ∃ n : ℕ, Odd n ∧ Weird n ∧ 947 ≤ n ∧ ¬ (945 ∣ n) ∧ ∀ d, d ∣ n → ¬ Semiperfect d := by
  constructor
  · rintro ⟨n, hodd, hw⟩
    exact ⟨n, hodd, hw, odd_weird_ge_947 hodd hw, hw.not_dvd_945,
      fun d hd => hw.no_semiperfect_divisor hd⟩
  · rintro ⟨n, hodd, hw, -⟩
    exact ⟨n, hodd, hw⟩

end WeirdNumbers
end Brockian

