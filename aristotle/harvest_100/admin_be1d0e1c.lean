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

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; note `W 0 = 0`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- A *Woodall prime* is a prime of the form `n * 2 ^ n - 1` with `n ≥ 1`. -/
def IsWoodallPrime (p : ℕ) : Prop := p.Prime ∧ ∃ n, 0 < n ∧ woodall n = p

/-- **The Woodall prime infinitude conjecture**: there are infinitely many Woodall primes.
This is an open problem; the statement is recorded here and reduced to equivalent index
formulations below. -/
def WoodallPrimeInfinitude : Prop := {p : ℕ | IsWoodallPrime p}.Infinite

/-! ## Basic arithmetic of Woodall numbers -/

theorem one_le_mul_two_pow {n : ℕ} (hn : 0 < n) : 1 ≤ n * 2 ^ n :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne' (pow_ne_zero _ two_ne_zero))

theorem woodall_add_one {n : ℕ} (hn : 0 < n) : woodall n + 1 = n * 2 ^ n :=
  Nat.sub_add_cancel (one_le_mul_two_pow hn)

theorem woodall_zero : woodall 0 = 0 := rfl

theorem woodall_one : woodall 1 = 1 := rfl

theorem woodall_two : woodall 2 = 7 := rfl

theorem woodall_three : woodall 3 = 23 := rfl

theorem woodall_six : woodall 6 = 383 := rfl

/-- `woodall` is monotone on all of `ℕ`. -/
theorem woodall_monotone : Monotone woodall := by
  intro m n hmn
  have h : m * 2 ^ m ≤ n * 2 ^ n :=
    Nat.mul_le_mul hmn (Nat.pow_le_pow_right (by norm_num) hmn)
  exact Nat.sub_le_sub_right h 1

/-- On indices `≥ 1`, `woodall` is strictly increasing. -/
theorem woodall_lt_woodall {m n : ℕ} (hm : 0 < m) (hmn : m < n) : woodall m < woodall n := by
  have hn : 0 < n := hm.trans hmn
  have h : m * 2 ^ m < n * 2 ^ n :=
    Nat.mul_lt_mul_of_lt_of_le hmn (Nat.pow_le_pow_right (by norm_num) hmn.le)
      (by positivity)
  have h1 := woodall_add_one hm
  have h2 := woodall_add_one hn
  omega

/-- `woodall` is injective on positive indices. -/
theorem woodall_injOn : Set.InjOn woodall {n : ℕ | 0 < n} := by
  intro m hm n hn h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (woodall_lt_woodall hm hlt).ne
  · exact heq
  · exact absurd h.symm (woodall_lt_woodall hn hgt).ne

/-- Woodall numbers grow at least as fast as their index. -/
theorem le_woodall {n : ℕ} (hn : 0 < n) : n ≤ woodall n := by
  have h1 := woodall_add_one hn
  have h2 : 2 * n ≤ n * 2 ^ n := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 2 * n = n * 2 ^ 1 := by ring
      _ ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h
  omega

/-! ## Small Woodall primes -/

theorem isWoodallPrime_seven : IsWoodallPrime 7 := ⟨by norm_num, 2, by norm_num, woodall_two⟩

theorem isWoodallPrime_twentyThree : IsWoodallPrime 23 :=
  ⟨by norm_num, 3, by norm_num, woodall_three⟩

theorem isWoodallPrime_383 : IsWoodallPrime 383 := ⟨by norm_num, 6, by norm_num, woodall_six⟩

/-- There are at least three Woodall primes. -/
theorem three_le_card_woodallPrimes :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ IsWoodallPrime a ∧ IsWoodallPrime b ∧ IsWoodallPrime c :=
  ⟨7, 23, 383, by norm_num, by norm_num, isWoodallPrime_seven, isWoodallPrime_twentyThree,
    isWoodallPrime_383⟩

/-! ## An infinite family of composite Woodall numbers -/

theorem mul_two_pow_mod_three_of_mod_six_eq_four {n : ℕ} (h : n % 6 = 4) :
    n * 2 ^ n % 3 = 1 := by
  have h2 : 2 ^ n = 4 ^ (n / 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [h2, Nat.mul_mod, Nat.pow_mod]
  norm_num
  omega

theorem mul_two_pow_mod_three_of_mod_six_eq_five {n : ℕ} (h : n % 6 = 5) :
    n * 2 ^ n % 3 = 1 := by
  have h2 : 2 ^ n = 2 * 4 ^ (n / 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
    congr 1
    omega
  rw [h2, Nat.mul_mod, Nat.mul_mod 2 (4 ^ (n / 2)), Nat.pow_mod]
  norm_num
  omega

/-- If `n ≡ 4` or `5 (mod 6)` then `3 ∣ W n`. -/
theorem three_dvd_woodall {n : ℕ} (h : n % 6 = 4 ∨ n % 6 = 5) : 3 ∣ woodall n := by
  have hn : 0 < n := by omega
  have hmod : n * 2 ^ n % 3 = 1 := by
    rcases h with h | h
    · exact mul_two_pow_mod_three_of_mod_six_eq_four h
    · exact mul_two_pow_mod_three_of_mod_six_eq_five h
  have hdm := Nat.div_add_mod (n * 2 ^ n) 3
  have h1 := woodall_add_one hn
  exact ⟨n * 2 ^ n / 3, by omega⟩

/-- Woodall numbers with index `≡ 4, 5 (mod 6)` are composite. -/
theorem not_prime_woodall_of_mod_six {n : ℕ} (h : n % 6 = 4 ∨ n % 6 = 5) :
    ¬ (woodall n).Prime := by
  intro hp
  have hdvd := three_dvd_woodall h
  have h3 : (3 : ℕ) = woodall n :=
    (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd).resolve_left (by norm_num)
  have h4 : 4 ≤ n := by omega
  have hle : woodall 4 ≤ woodall n := woodall_monotone h4
  have h63 : woodall 4 = 63 := rfl
  omega

/-- There are infinitely many composite Woodall numbers. -/
theorem infinite_composite_woodall_indices :
    {n : ℕ | 0 < n ∧ ¬ (woodall n).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  exact ⟨6 * (a + 1) + 4, ⟨by omega, not_prime_woodall_of_mod_six (Or.inl (by omega))⟩, by omega⟩

/-! ## The main reduction -/

/-- **Reduction of the conjecture to an index statement.** There are infinitely many Woodall
primes if and only if for every bound `N` there is some index `n > N` with `n * 2 ^ n - 1`
prime. -/
theorem woodallPrimeInfinitude_iff :
    WoodallPrimeInfinitude ↔ ∀ N : ℕ, ∃ n, N < n ∧ (woodall n).Prime := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hlt⟩ := hinf.exists_gt (woodall N)
    obtain ⟨hprime, n, hn, hpn⟩ := hp
    refine ⟨n, ?_, hpn ▸ hprime⟩
    by_contra hle
    push_neg at hle
    have := woodall_monotone hle
    omega
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h (a + 1)
    have hpos : 0 < n := by omega
    refine ⟨woodall n, ⟨hp, n, hpos, rfl⟩, ?_⟩
    have := le_woodall hpos
    omega

/-- Equivalent form: there are infinitely many Woodall primes iff the set of indices giving
Woodall primes is infinite. -/
theorem woodallPrimeInfinitude_iff_indices_infinite :
    WoodallPrimeInfinitude ↔ {n : ℕ | 0 < n ∧ (woodall n).Prime}.Infinite := by
  rw [woodallPrimeInfinitude_iff]
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h a
    exact ⟨n, ⟨by omega, hp⟩, hn⟩
  · intro hinf N
    obtain ⟨n, hn, hlt⟩ := hinf.exists_gt N
    exact ⟨n, hlt, hn.2⟩

/-- A sharpened reduction: since indices `≡ 4, 5 (mod 6)` always give composite Woodall
numbers, the conjecture is equivalent to the existence of arbitrarily large prime-producing
indices among `n ≡ 0, 1, 2, 3 (mod 6)`. -/
theorem woodallPrimeInfinitude_iff_restricted :
    WoodallPrimeInfinitude ↔
      ∀ N : ℕ, ∃ n, N < n ∧ (n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3) ∧
        (woodall n).Prime := by
  rw [woodallPrimeInfinitude_iff]
  constructor
  · intro h N
    obtain ⟨n, hn, hp⟩ := h N
    have hnc : ¬ (n % 6 = 4 ∨ n % 6 = 5) := fun hc => not_prime_woodall_of_mod_six hc hp
    exact ⟨n, hn, by omega, hp⟩
  · intro h N
    obtain ⟨n, hn, _, hp⟩ := h N
    exact ⟨n, hn, hp⟩

end Brockian.CullenWoodall

