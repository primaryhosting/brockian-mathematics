/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality, stated in the usual way: `p` is at least `2` and its only divisors are
`1` and `p`. (This file is self-contained, so the predicate is spelled out here.) -/
def GwPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- Trial division by all candidate divisors `d ≤ 32`; correct for `p ≤ 1051`
since `33 * 33 = 1089 > 1051`. -/
def gwNoSmallDiv (p : Nat) : Bool :=
  (List.range 33).all fun d => decide (d < 2) || decide (p < d * d) || decide (p % d ≠ 0)

/-- Boolean primality test, sound for arguments `p ≤ 1051`. -/
def gwIsPrime (p : Nat) : Bool := decide (2 ≤ p) && gwNoSmallDiv p

theorem gwIsPrime_sound {p : Nat} (hp : p ≤ 1051) (h : gwIsPrime p = true) : GwPrime p := by
  rw [gwIsPrime, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hdiv⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  exfalso
  obtain ⟨k, hk⟩ := hm
  -- both factors are at least 2
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, Nat.zero_mul] at hk; omega
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0, Nat.mul_zero] at hk; omega
  have hk1 : k ≠ 1 := by
    intro h1; rw [h1, Nat.mul_one] at hk; omega
  have hm2 : 2 ≤ m := by omega
  have hk2 : 2 ≤ k := by omega
  -- the smaller factor `d` satisfies `d * d ≤ p`
  obtain ⟨d, hd⟩ : ∃ d, min m k = d := ⟨_, rfl⟩
  have hdor : d = m ∨ d = k := by
    rw [← hd]
    rcases Nat.le_total m k with h | h
    · exact Or.inl (Nat.min_eq_left h)
    · exact Or.inr (Nat.min_eq_right h)
  have hdm : d ≤ m := hd ▸ Nat.min_le_left m k
  have hdk : d ≤ k := hd ▸ Nat.min_le_right m k
  have hd2 : 2 ≤ d := by omega
  have hdd : d * d ≤ p := by
    calc d * d ≤ m * k := Nat.mul_le_mul hdm hdk
    _ = p := hk.symm
  have hd32 : d < 33 := by
    rcases Nat.lt_or_ge d 33 with h | h
    · exact h
    · exfalso
      have : 33 * 33 ≤ d * d := Nat.mul_le_mul h h
      omega
  -- `d` divides `p`, contradicting the trial division check
  have hmod : p % d = 0 := by
    rcases hdor with hde | hde
    · rw [hde, hk]
      exact Nat.mul_mod_right m k
    · rw [hde, hk]
      exact Nat.mul_mod_left m k
  have hmem : d ∈ List.range 33 := List.mem_range.mpr hd32
  have := List.all_eq_true.mp hdiv d hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq] at this
  omega

/-- The "wheel" of small prime shifts: for every even `n` with `4 ≤ n ≤ 1051`
one of these primes `p` satisfies `n - p` prime. -/
def gwK2Wheel : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- Boolean test: `n = p + q` for some `p` in the wheel and some prime `q`. -/
def gwK2Check (n : Nat) : Bool :=
  gwK2Wheel.any fun p => gwIsPrime p && decide (p ≤ n) && gwIsPrime (n - p)

theorem gwK2Check_sound {n : Nat} (hn : n ≤ 1051) (h : gwK2Check n = true) :
    ∃ p q : Nat, GwPrime p ∧ GwPrime q ∧ p + q = n := by
  rw [gwK2Check, List.any_eq_true] at h
  obtain ⟨p, _, hp⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hp1, hple⟩, hp3⟩ := hp
  exact ⟨p, n - p, gwIsPrime_sound (by omega) hp1, gwIsPrime_sound (by omega) hp3, by omega⟩

/-- The wheel test succeeds for every even `n` with `4 ≤ n ≤ 1051`. -/
theorem gwK2Check_range :
    (List.range 1052).all
      (fun n => decide (n < 4) || decide (n % 2 = 1) || gwK2Check n) = true := by
  decide +kernel

/-- **Goldbach Wheel K 2, modulus 1051.**
Every even `n` with `4 ≤ n ≤ 1051` is a sum of two primes. -/
theorem GoldbachWheelK2_1051 :
    ∀ n : Nat, 4 ≤ n → n ≤ 1051 → n % 2 = 0 →
      ∃ p q : Nat, GwPrime p ∧ GwPrime q ∧ p + q = n := by
  intro n h4 hle hev
  have hmem : n ∈ List.range 1052 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp gwK2Check_range n hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · omega
  · omega
  · exact gwK2Check_sound hle h

end Brockian

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

import Mathlib
import RequestProject.GoldbachWheelK2_1051

/-!
Sanity companion to `RequestProject/GoldbachWheelK2_1051.lean`: the self-contained
primality predicate `Brockian.GwPrime` used there agrees with `Nat.Prime`, so the
main theorem is the expected Goldbach statement.
-/

namespace Brockian

theorem gwPrime_iff_prime (p : Nat) : GwPrime p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨h2, hdiv⟩
    refine Nat.prime_def.mpr ⟨h2, ?_⟩
    intro m hm
    exact hdiv m hm
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- Every even `n` with `4 ≤ n ≤ 1051` is a sum of two primes, stated with `Nat.Prime`. -/
theorem goldbachWheelK2_1051_prime :
    ∀ n : Nat, 4 ≤ n → n ≤ 1051 → Even n →
      ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n h4 hle hev
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_1051 n h4 hle (Nat.even_iff.mp hev)
  exact ⟨p, q, (gwPrime_iff_prime p).mp hp, (gwPrime_iff_prime q).mp hq, hpq⟩

end Brockian

