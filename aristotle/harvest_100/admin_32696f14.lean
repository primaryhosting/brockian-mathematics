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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

@[simp] lemma woodall_one : woodall 1 = 1 := by decide
@[simp] lemma woodall_two : woodall 2 = 7 := by decide
@[simp] lemma woodall_three : woodall 3 = 23 := by decide

/-- `7 = W 2` is a Woodall prime. -/
lemma prime_woodall_two : Nat.Prime (woodall 2) := by
  rw [woodall_two]; norm_num

/-- `23 = W 3` is a Woodall prime. -/
lemma prime_woodall_three : Nat.Prime (woodall 3) := by
  rw [woodall_three]; norm_num

/-- `383 = W 6` is a Woodall prime. -/
lemma prime_woodall_six : Nat.Prime (woodall 6) := by
  have h : woodall 6 = 383 := by decide
  rw [h]; norm_num

lemma one_le_mul_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

/-- Woodall numbers grow at least linearly: `n ≤ W n` for `n ≥ 1`. -/
lemma le_woodall {n : ℕ} (hn : 1 ≤ n) : n ≤ woodall n := by
  have h2 : 2 * n ≤ n * 2 ^ n := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 2 * n = n * 2 ^ 1 := by ring
      _ ≤ n * 2 ^ n := Nat.mul_le_mul_left _ hp
  unfold woodall
  omega

/-- The powers of two modulo three alternate between `1` and `2`. -/
lemma two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : 2 ^ (k + 1) % 3 = (2 * (2 ^ k % 3)) % 3 := by
        rw [pow_succ]
        omega
      rcases Nat.even_or_odd k with hk | hk
      · have hk0 : k % 2 = 0 := Nat.even_iff.mp hk
        simp only [hk0] at ih
        rw [h, ih]
        have hs : (k + 1) % 2 = 1 := by omega
        simp [hs]
      · have hk1 : k % 2 = 1 := Nat.odd_iff.mp hk
        simp only [hk1, if_neg (by norm_num : ¬ (1 : ℕ) = 0)] at ih
        rw [h, ih]
        have hs : (k + 1) % 2 = 0 := by omega
        simp [hs]

/-- If `n ≡ 4` or `n ≡ 5 (mod 6)` then `3 ∣ W n`. -/
theorem three_dvd_woodall {n : ℕ} (hn : n % 6 = 4 ∨ n % 6 = 5) : 3 ∣ woodall n := by
  have hmul : n * 2 ^ n % 3 = 1 := by
    rw [Nat.mul_mod]
    rcases hn with h | h
    · have h2 : n % 2 = 0 := by omega
      have h3 : n % 3 = 1 := by omega
      rw [two_pow_mod_three, h3, if_pos h2]
    · have h2 : n % 2 = 1 := by omega
      have h3 : n % 3 = 2 := by omega
      rw [two_pow_mod_three, h3, if_neg (by omega : ¬ n % 2 = 0)]
  have h1 : 1 ≤ n * 2 ^ n := by
    rcases hn with h | h <;> exact one_le_mul_pow (by omega)
  unfold woodall
  omega

/-- Woodall numbers are large: `4 ≤ n` implies `3 < W n`. -/
lemma lt_woodall_of_four_le {n : ℕ} (hn : 4 ≤ n) : 3 < woodall n :=
  lt_of_lt_of_le (by omega) (le_woodall (by omega))

/-- For `n ≥ 4` with `n ≡ 4, 5 (mod 6)`, the Woodall number `W n` is composite. -/
theorem not_prime_woodall {n : ℕ} (hn : 4 ≤ n) (h : n % 6 = 4 ∨ n % 6 = 5) :
    ¬ Nat.Prime (woodall n) := by
  intro hp
  have hdvd : 3 ∣ woodall n := three_dvd_woodall h
  have h13 := hp.eq_one_or_self_of_dvd 3 hdvd
  have hbig := lt_woodall_of_four_le hn
  omega

/-- There are infinitely many `n` for which the Woodall number `W n` is composite. -/
theorem infinite_composite_woodall : {n : ℕ | ¬ Nat.Prime (woodall n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  exact ⟨6 * (a + 1) + 4, not_prime_woodall (by omega) (Or.inl (by omega)), by omega⟩

/-- A Woodall prime: a prime of the form `n * 2 ^ n - 1` with `n ≥ 1`. -/
def IsWoodallPrime (p : ℕ) : Prop := Nat.Prime p ∧ ∃ n, 1 ≤ n ∧ p = woodall n

lemma isWoodallPrime_seven : IsWoodallPrime 7 :=
  ⟨by norm_num, 2, by norm_num, by simp⟩

/--
**Woodall prime infinitude (conditional reduction).**

The infinitude of Woodall primes is an open problem.  What is proved here is the
reduction: *if* the indices `n` at which `n * 2 ^ n - 1` is prime are unbounded,
*then* the set of Woodall primes is infinite.
-/
theorem WoodallPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (woodall n)) :
    {p : ℕ | IsWoodallPrime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hp⟩ := h a
  exact ⟨woodall n, ⟨hp, n, by omega, rfl⟩, lt_of_lt_of_le hn (le_woodall (by omega))⟩

end Brockian.CullenWoodall

