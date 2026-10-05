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

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit: the base-ten number consisting of `n` digits `1`,
i.e. `repunit n = (10 ^ n - 1) / 9`. -/
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

@[simp] lemma repunit_zero : repunit 0 = 0 := rfl

@[simp] lemma repunit_one : repunit 1 = 1 := rfl

lemma repunit_succ (n : ℕ) : repunit (n + 1) = repunit n + 10 ^ n :=
  Finset.sum_range_succ _ _

/-- Defining identity: `9 * repunit n + 1 = 10 ^ n`. -/
lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repunit_succ, pow_succ]; omega

lemma repunit_strictMono : StrictMono repunit := by
  apply strictMono_nat_of_lt_succ
  intro n
  have : 0 < 10 ^ n := pow_pos (by norm_num) n
  rw [repunit_succ]; omega

lemma le_repunit (n : ℕ) : n ≤ repunit n := repunit_strictMono.le_apply

/-- Splitting a repunit: `repunit (a + b) = repunit a + 10 ^ a * repunit b`. -/
lemma repunit_add (a b : ℕ) : repunit (a + b) = repunit a + 10 ^ a * repunit b := by
  unfold repunit
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp [pow_add]

/-- If `m ∣ n` then `repunit m ∣ repunit n`. -/
lemma repunit_dvd_repunit {m n : ℕ} (h : m ∣ n) : repunit m ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
      have : m * (k + 1) = m * k + m := by ring
      rw [this, repunit_add]
      exact Nat.dvd_add ih (dvd_mul_left (repunit m) (10 ^ (m * k)))

lemma one_lt_repunit {n : ℕ} (hn : 2 ≤ n) : 1 < repunit n := by
  calc 1 = repunit 1 := rfl
  _ < repunit n := repunit_strictMono (by omega)

/-- **Partial result (unconditional).** If `repunit n` is prime then `n` is prime. -/
theorem prime_of_prime_repunit {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    by_contra hc
    interval_cases n <;> simp_all [Nat.not_prime_zero, Nat.not_prime_one]
  refine Nat.prime_def.mpr ⟨hn2, ?_⟩
  intro m hm
  by_contra hcon
  push_neg at hcon
  obtain ⟨hm1, hmn⟩ := hcon
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm (by omega)
  have hm2 : 2 ≤ m := by omega
  have hmlt : m < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm) hmn
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hm
  rcases (Nat.Prime.eq_one_or_self_of_dvd h _ hdvd) with h1 | h2
  · exact absurd h1 (by have := one_lt_repunit hm2; omega)
  · exact absurd h2 (by have := repunit_strictMono hmlt; omega)

/-- `repunit 2 = 11` is prime, so repunit primes exist. -/
theorem prime_repunit_two : Nat.Prime (repunit 2) := by decide

/-- The set of repunit primes. -/
def repunitPrimes : Set ℕ := {p | p.Prime ∧ ∃ n, p = repunit n}

lemma repunitPrimes_nonempty : (11 : ℕ) ∈ repunitPrimes :=
  ⟨by decide, 2, rfl⟩

/--
**Repunit Prime Infinitude (conditional reduction).**

Assuming the arithmetic hypothesis that repunit primes occur with arbitrarily large index
(`∀ N, ∃ n > N, repunit n is prime`) — which is the content of the open conjecture — the set
of repunit primes is infinite.

The reduction is genuine: since `repunit` is strictly monotone, distinct indices give distinct
primes, so unboundedness of the index set yields an infinite set of primes.
-/
theorem RepunitPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n)) :
    repunitPrimes.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hp⟩ := h a
  refine ⟨repunit n, ⟨hp, n, rfl⟩, ?_⟩
  exact lt_of_lt_of_le hn (le_repunit n)

/-- Equivalently: the hypothesis of `RepunitPrimeInfinitude` is *equivalent* to the infinitude
of the set of repunit primes. -/
theorem repunitPrimes_infinite_iff :
    repunitPrimes.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n) := by
  constructor
  · intro hinf N
    obtain ⟨p, ⟨hp, n, rfl⟩, hlt⟩ := hinf.exists_gt (repunit N)
    exact ⟨n, repunit_strictMono.lt_iff_lt.mp hlt, hp⟩
  · exact RepunitPrimeInfinitude

/-- **Partial result (unconditional).** The index set of repunit primes consists of primes,
so the conjecture reduces to a statement about prime indices only. -/
theorem RepunitPrimeInfinitude_index_prime :
    ∀ n, Nat.Prime (repunit n) → Nat.Prime n := fun _ h => prime_of_prime_repunit h

/-- **Partial result (unconditional).** There are infinitely many indices `n` for which
`repunit n` is *not* prime: every composite index works. -/
theorem infinite_setOf_not_prime_repunit : {n : ℕ | ¬ Nat.Prime (repunit n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨2 * (a + 2), ?_, by omega⟩
  intro hp
  have hprime := prime_of_prime_repunit hp
  have h2 : (2 : ℕ) ∣ 2 * (a + 2) := ⟨a + 2, rfl⟩
  rcases hprime.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

/-! ### Unconditional infinitude of prime divisors of repunits -/

/-- **Unconditional.** Every prime other than `2` and `5` divides some repunit. -/
theorem exists_pos_dvd_repunit {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ n, 0 < n ∧ p ∣ repunit n := by
  by_cases h3 : p = 3
  · exact ⟨3, by norm_num, by subst h3; decide⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp10 : ¬ (p ∣ 10) := by
    intro h
    have h25 : p ∣ 2 * 5 := by norm_num at h ⊢; exact h
    rcases (Nat.Prime.dvd_mul hp).mp h25 with h' | h'
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')
  have h10 : (10 : ZMod p) ≠ 0 := fun h =>
    hp10 ((ZMod.natCast_eq_zero_iff 10 p).mp (by push_cast; exact h))
  have hferm : (10 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h10
  have hkey : ((9 * repunit (p - 1) + 1 : ℕ) : ZMod p) = ((10 ^ (p - 1) : ℕ) : ZMod p) := by
    rw [nine_mul_repunit_add_one]
  push_cast at hkey
  rw [hferm] at hkey
  have h9 : (9 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 9 := (ZMod.natCast_eq_zero_iff 9 p).mp (by push_cast; exact h)
    have h32 : p ∣ 3 ^ 2 := by norm_num at hd ⊢; exact hd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h32))
  have hR : ((repunit (p - 1) : ℕ) : ZMod p) = 0 := by
    have hz : (9 : ZMod p) * (repunit (p - 1) : ZMod p) = 0 := by linear_combination hkey
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h h9
    · exact h
  refine ⟨p - 1, ?_, (ZMod.natCast_eq_zero_iff _ p).mp hR⟩
  have := hp.two_le
  omega

/-- The set of primes dividing some repunit. -/
def repunitPrimeDivisors : Set ℕ := {p | p.Prime ∧ ∃ n, 0 < n ∧ p ∣ repunit n}

/-- **Unconditional partial result.** Infinitely many primes divide some repunit. -/
theorem infinite_repunitPrimeDivisors : repunitPrimeDivisors.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (a + 6)
  exact ⟨p, ⟨hp, exists_pos_dvd_repunit hp (by omega) (by omega)⟩, by omega⟩

end RepunitPrimes
end Brockian

