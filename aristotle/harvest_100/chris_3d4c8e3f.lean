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

/-- The `n`-th base-ten repunit `Rₙ = 1 + 10 + ⋯ + 10ⁿ⁻¹ = (10ⁿ - 1)/9`. -/
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

@[simp] lemma repunit_zero : repunit 0 = 0 := rfl
@[simp] lemma repunit_one : repunit 1 = 1 := rfl

/-- The defining identity `9 · Rₙ + 1 = 10ⁿ`. -/
lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repunit, Finset.sum_range_succ, ← repunit, pow_succ]
      omega

lemma one_lt_repunit {n : ℕ} (hn : 2 ≤ n) : 1 < repunit n := by
  have h := nine_mul_repunit_add_one n
  have : (10:ℕ) ^ 2 ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  norm_num at this
  omega

/-- Repunits with positive index are odd. -/
lemma repunit_odd {n : ℕ} (hn : 0 < n) : ¬ (2 ∣ repunit n) := by
  intro h
  have h9 := nine_mul_repunit_add_one n
  have h2 : (2:ℕ) ∣ 10 ^ n := dvd_pow (by norm_num) hn.ne'
  omega

/-- A repunit is congruent to its index modulo `3` (its digit sum is `n`). -/
lemma repunit_mod_three (n : ℕ) : repunit n % 3 = n % 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : 10 ^ n % 3 = 1 := by rw [Nat.pow_mod]; norm_num
      rw [repunit, Finset.sum_range_succ, ← repunit]
      omega

/-- Divisibility of indices gives divisibility of repunits. -/
lemma repunit_dvd_repunit {m n : ℕ} (h : m ∣ n) : repunit m ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  have key : (9 * repunit m) ∣ (9 * repunit (m * k)) := by
    have h1 : 9 * repunit m + 1 = 10 ^ m := nine_mul_repunit_add_one m
    have h2 : 9 * repunit (m * k) + 1 = 10 ^ (m * k) := nine_mul_repunit_add_one (m * k)
    have hsub : (10 ^ m - 1 : ℤ) ∣ ((10 ^ m) ^ k - 1 : ℤ) := by
      simpa using sub_dvd_pow_sub_pow ((10:ℤ) ^ m) 1 k
    have hz : ((9 * repunit m : ℕ) : ℤ) ∣ ((9 * repunit (m * k) : ℕ) : ℤ) := by
      have e1 : ((9 * repunit m : ℕ) : ℤ) = (10:ℤ) ^ m - 1 := by
        have := congrArg (fun t : ℕ => (t : ℤ)) h1
        push_cast at this ⊢
        linarith
      have e2 : ((9 * repunit (m * k) : ℕ) : ℤ) = ((10:ℤ) ^ m) ^ k - 1 := by
        have := congrArg (fun t : ℕ => (t : ℤ)) h2
        push_cast at this ⊢
        rw [← pow_mul]
        linarith
      rw [e1, e2]; exact hsub
    exact_mod_cast hz
  exact (mul_dvd_mul_iff_left (by norm_num : (9:ℕ) ≠ 0)).mp key

/-- If a repunit `Rₙ` is prime, then its index `n` is prime. -/
theorem prime_index_of_prime_repunit {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    by_contra hlt
    interval_cases n
    · exact absurd h (by norm_num [repunit_zero])
    · exact absurd h (by norm_num [repunit_one])
  refine Nat.prime_def.mpr ⟨hn2, ?_⟩
  intro m hm
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hm
  rcases h.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · left
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · simp [repunit_zero] at h1
      · rfl
    · exact absurd h1 (one_lt_repunit hm2).ne'
  · right
    have hmn : m ≤ n := Nat.le_of_dvd (by omega) hm
    rcases lt_or_eq_of_le hmn with hlt | heq
    · exfalso
      have hstep : repunit m + 10 ^ m ≤ repunit n := by
        have hss : Finset.range (m + 1) ⊆ Finset.range n :=
          Finset.range_subset_range.mpr (by omega : m + 1 ≤ n)
        have hsub : repunit (m + 1) ≤ repunit n := Finset.sum_le_sum_of_subset hss
        simpa [repunit, Finset.sum_range_succ] using hsub
      have : 0 < (10:ℕ) ^ m := pow_pos (by norm_num) m
      omega
    · exact heq

/-- **Key congruence.** For a prime index `p ∉ {2, 3}`, every prime divisor `q` of the
repunit `R_p` satisfies `q ≡ 1 (mod 2p)`. -/
theorem prime_divisor_mod {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hp2 : p ≠ 2)
    (hq : q.Prime) (hdvd : q ∣ repunit p) : q % (2 * p) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hppos : 0 < p := hp.pos
  have hq2 : q ≠ 2 := by
    rintro rfl; exact repunit_odd hppos hdvd
  have hr : ((repunit p : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have h9dvd : q ∣ 9 * repunit p := hdvd.mul_left 9
  -- `q` cannot divide `10`, since `q ∣ R_p` and `9 R_p + 1 = 10 ^ p`
  have hne : ((10 : ℕ) : ZMod q) ≠ 0 := by
    intro h
    have hd : q ∣ 10 := (ZMod.natCast_eq_zero_iff _ _).mp h
    have hdp : q ∣ 10 ^ p := hd.trans (dvd_pow_self 10 hppos.ne')
    have h1 : q ∣ 1 := by
      have := Nat.dvd_sub hdp h9dvd
      rwa [show 10 ^ p - 9 * repunit p = 1 by have := nine_mul_repunit_add_one p; omega] at this
    exact Nat.Prime.one_lt hq |>.ne' (Nat.dvd_one.mp h1)
  have hq3 : q ≠ 3 := by
    rintro rfl
    have h3 : (3:ℕ) ∣ p := by
      have := repunit_mod_three p
      omega
    exact hp3 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h3)).symm
  -- `10` has order exactly `p` modulo `q`
  have hten : ((10 : ℕ) : ZMod q) ^ p = 1 := by
    have h9 := nine_mul_repunit_add_one p
    have h10 : ((10 ^ p : ℕ) : ZMod q) = ((9 * repunit p + 1 : ℕ) : ZMod q) := by rw [h9]
    push_cast at h10 ⊢
    rw [h10, hr]
    ring
  have hord : orderOf ((10 : ℕ) : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one hten
  have hordp : orderOf ((10 : ℕ) : ZMod q) = p := by
    rcases hp.eq_one_or_self_of_dvd _ hord with h1 | h1
    · exfalso
      have h10 : ((10 : ℕ) : ZMod q) = 1 := orderOf_eq_one_iff.mp h1
      have h9z : ((9 : ℕ) : ZMod q) = 0 := by push_cast at h10 ⊢; linear_combination h10
      have h9 : q ∣ 9 := (ZMod.natCast_eq_zero_iff _ _).mp h9z
      have hle := Nat.le_of_dvd (by norm_num) h9
      interval_cases q <;> simp_all (config := {decide := true})
    · exact h1
  have hFermat : ((10 : ℕ) : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hpq : p ∣ q - 1 := by
    have := orderOf_dvd_of_pow_eq_one hFermat
    rwa [hordp] at this
  have h2q : 2 ∣ q - 1 := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    omega
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2q hpq
  have hq1 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
  have hqk : q = 2 * p * k + 1 := by omega
  rw [hqk, show 2 * p * k + 1 = 1 + 2 * p * k by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega)]

/-- **Conditional infinitude of repunit primes.**

If there are arbitrarily large prime indices `p` for which the repunit `R_p` has no prime
divisor `q ≡ 1 (mod 2p)` with `q² ≤ R_p` — i.e. `R_p` survives the trial division to which
its prime divisors are restricted by `prime_divisor_mod` — then there are infinitely many
repunit primes.

This is a Lean-checked reduction of the (open) Brockian conjecture on the infinitude of
repunit primes to a "no small admissible factor" hypothesis. -/
theorem RepunitPrimeInfinitude
    (H : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
      ∀ q : ℕ, q.Prime → q % (2 * p) = 1 → q * q ≤ repunit p → ¬ q ∣ repunit p) :
    {n : ℕ | Nat.Prime (repunit n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hp, hsmall⟩ := H (max N 5)
  have hp5 : 5 ≤ p := le_of_lt (lt_of_le_of_lt (le_max_right N 5) hpN)
  have hpN' : N < p := lt_of_le_of_lt (le_max_left N 5) hpN
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h1 : 1 < repunit p := one_lt_repunit (by omega)
  refine ⟨p, ?_, hpN'⟩
  show Nat.Prime (repunit p)
  by_contra hnp
  have hqp : (repunit p).minFac.Prime := Nat.minFac_prime (by omega)
  have hqdvd : (repunit p).minFac ∣ repunit p := Nat.minFac_dvd _
  have hsq : (repunit p).minFac * (repunit p).minFac ≤ repunit p := by
    have := Nat.minFac_sq_le_self (by omega : 0 < repunit p) hnp
    nlinarith [this]
  exact hsmall _ hqp (prime_divisor_mod hp hp3 hp2 hqp hqdvd) hsq hqdvd

/-- Non-vacuity check: `R₂ = 11` is a repunit prime, so the set studied above is nonempty. -/
lemma prime_repunit_two : Nat.Prime (repunit 2) := by
  have : repunit 2 = 11 := by decide
  rw [this]; norm_num

/-- The hypothesis of `RepunitPrimeInfinitude` is in fact *equivalent* to the infinitude of
repunit primes: the conjecture is exactly the statement that arbitrarily large prime indices `p`
exist for which `R_p` has no admissible prime factor `q ≡ 1 (mod 2p)` with `q² ≤ R_p`. -/
theorem repunitPrimeInfinitude_iff :
    {n : ℕ | Nat.Prime (repunit n)}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
        ∀ q : ℕ, q.Prime → q % (2 * p) = 1 → q * q ≤ repunit p → ¬ q ∣ repunit p := by
  refine ⟨fun hinf N => ?_, RepunitPrimeInfinitude⟩
  obtain ⟨p, hpmem, hpgt⟩ := hinf.exists_gt (max N 5)
  have hprime : Nat.Prime (repunit p) := hpmem
  have hp5 : 5 ≤ p := le_of_lt (lt_of_le_of_lt (le_max_right N 5) hpgt)
  refine ⟨p, lt_of_le_of_lt (le_max_left N 5) hpgt, prime_index_of_prime_repunit hprime,
    fun q hq _ hsq hdvd => ?_⟩
  have hqeq : q = repunit p := ((Nat.prime_dvd_prime_iff_eq hq hprime).mp hdvd)
  have h1 : 1 < repunit p := one_lt_repunit (by omega)
  subst hqeq
  nlinarith

end Brockian.RepunitPrimes

