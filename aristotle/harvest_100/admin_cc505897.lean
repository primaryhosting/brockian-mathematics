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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

open Finset

/-- The `n`-th base-ten repunit `1, 11, 111, ...` (with `repunit 0 = 0`). -/
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

@[simp] lemma repunit_zero : repunit 0 = 0 := rfl

@[simp] lemma repunit_one : repunit 1 = 1 := rfl

lemma repunit_succ (n : ℕ) : repunit (n + 1) = repunit n + 10 ^ n := by
  simp [repunit, Finset.sum_range_succ]

lemma repunit_add (m n : ℕ) : repunit (m + n) = repunit m + 10 ^ m * repunit n := by
  rw [repunit, repunit, repunit, Finset.sum_range_add, Finset.mul_sum]
  simp [pow_add]

/-- The closed form: `9 * Rₙ + 1 = 10 ^ n`. -/
lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repunit_succ, pow_succ]; omega

lemma repunit_strictMono : StrictMono repunit := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have : 0 < 10 ^ n := pow_pos (by norm_num) n
  rw [repunit_succ]; omega

lemma repunit_injective : Function.Injective repunit := repunit_strictMono.injective

lemma le_repunit (n : ℕ) : n ≤ repunit n := repunit_strictMono.le_apply

/-- Repunits are divisibility-monotone in their index. -/
lemma repunit_dvd_repunit {m n : ℕ} (h : m ∣ n) : repunit m ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
      have hmk : m * (k + 1) = m * k + m := by ring
      rw [hmk, repunit_add]
      exact Dvd.dvd.add ih (Dvd.dvd.mul_left dvd_rfl _)

/-- If a repunit is prime, then its index is prime. -/
theorem prime_index_of_repunit_prime {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push_neg at hlt
    interval_cases n <;> exact absurd h (by decide)
  refine Nat.prime_def.mpr ⟨hn2, fun m hm => ?_⟩
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hm
  rcases h.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · left
    have : repunit m = repunit 1 := by simpa using h1
    exact repunit_injective this
  · right
    exact repunit_injective h1

/-!
## Which primes divide repunits

Every prime other than `2` and `5` divides some (positive-index) repunit; in particular
infinitely many primes occur as divisors of repunits.
-/

theorem exists_repunit_dvd_of_prime {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ n, 0 < n ∧ p ∣ repunit n := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases h3 : p = 3
  · refine ⟨3, by norm_num, ?_⟩
    subst h3
    norm_num [repunit, Finset.sum_range_succ]
  -- `10` is invertible mod `p`, so `p ∣ 10 ^ (p - 1) - 1 = 9 * R_{p-1}`
  have hp10 : ¬ (p ∣ 10) := by
    intro hd
    have h1 : p ∣ 2 * 5 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have h10 : (10 : ZMod p) ≠ 0 := by
    intro h
    refine hp10 ((ZMod.natCast_eq_zero_iff 10 p).mp ?_)
    push_cast
    exact h
  have hferm : (10 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h10
  have hdvd9 : p ∣ 9 * repunit (p - 1) := by
    have hcast : ((9 * repunit (p - 1) + 1 : ℕ) : ZMod p) = 1 := by
      rw [nine_mul_repunit_add_one]
      push_cast
      exact hferm
    have : ((9 * repunit (p - 1) : ℕ) : ZMod p) = 0 := by
      push_cast at hcast ⊢
      linear_combination hcast
    exact (ZMod.natCast_eq_zero_iff _ p).mp this
  have hp9 : ¬ (p ∣ 9) := by
    intro hd
    have h1 : p ∣ 3 ^ 2 := by norm_num; exact hd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h1))
  have hcop : Nat.Coprime p 9 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hp9
  refine ⟨p - 1, ?_, ?_⟩
  · have := hp.two_le; omega
  · exact hcop.dvd_of_dvd_mul_left hdvd9

/-- Infinitely many primes divide some repunit. -/
theorem infinite_primes_dvd_repunit :
    {p : ℕ | Nat.Prime p ∧ ∃ n, 0 < n ∧ p ∣ repunit n}.Infinite := by
  have hsub : ({p : ℕ | Nat.Prime p} \ {2, 5}) ⊆
      {p : ℕ | Nat.Prime p ∧ ∃ n, 0 < n ∧ p ∣ repunit n} := by
    rintro p ⟨hp, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact ⟨hp, exists_repunit_dvd_of_prime hp hne.1 hne.2⟩
  exact Set.Infinite.mono hsub (Nat.infinite_setOf_prime.diff (Set.toFinite _))

/-!
## The main equivalence

The Brockian repunit-prime conjecture asserts that there are arbitrarily large `n` with `Rₙ`
prime.  The theorem below shows this is equivalent to the infinitude of the *set* of repunit
primes, and (by `prime_index_of_repunit_prime`) that any such index is itself prime.
-/

/-- The set of primes that are repunits. -/
def RepunitPrimeSet : Set ℕ := {p : ℕ | Nat.Prime p ∧ ∃ n, repunit n = p}

lemma repunit_two_eq : repunit 2 = 11 := by norm_num [repunit, Finset.sum_range_succ]

/-- `R₂ = 11` is a repunit prime, so the set of repunit primes is nonempty. -/
lemma repunitPrimeSet_nonempty : RepunitPrimeSet.Nonempty :=
  ⟨11, by norm_num, 2, repunit_two_eq⟩

/-- **Repunit prime infinitude (Lean-checked reduction).**
There are arbitrarily large indices `n` with `Rₙ` prime if and only if the set of repunit
primes is infinite. -/
theorem RepunitPrimeInfinitude :
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (repunit n)) ↔ RepunitPrimeSet.Infinite := by
  constructor
  · intro H
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨n, hn, hprime⟩ := H N
    exact ⟨repunit n, ⟨hprime, ⟨n, rfl⟩⟩, lt_of_lt_of_le hn (le_repunit n)⟩
  · intro H N
    obtain ⟨p, ⟨hp, n, rfl⟩, hlt⟩ := H.exists_gt (repunit N)
    exact ⟨n, repunit_strictMono.lt_iff_lt.mp hlt, hp⟩

/-- Every index of a repunit prime is itself prime, so the conjecture may equivalently be
stated over prime indices. -/
theorem RepunitPrimeInfinitude_prime_index :
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (repunit n)) ↔
      (∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime n ∧ Nat.Prime (repunit n)) := by
  constructor
  · intro H N
    obtain ⟨n, hn, hprime⟩ := H N
    exact ⟨n, hn, prime_index_of_repunit_prime hprime, hprime⟩
  · intro H N
    obtain ⟨n, hn, _, hprime⟩ := H N
    exact ⟨n, hn, hprime⟩

end Brockian.RepunitPrimes


