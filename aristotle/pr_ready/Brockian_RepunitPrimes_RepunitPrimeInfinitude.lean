/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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


/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

/-- The `n`-th base-ten repunit: the number `11…1` with `n` digits equal to `1`. -/
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

@[simp] lemma repunit_zero : repunit 0 = 0 := rfl

@[simp] lemma repunit_one : repunit 1 = 1 := rfl

lemma repunit_two : repunit 2 = 11 := rfl

/-- Splitting a repunit: `R (a + b) = R a + 10 ^ a * R b`. -/
lemma repunit_add (a b : ℕ) : repunit (a + b) = repunit a + 10 ^ a * repunit b := by
  unfold repunit
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp [pow_add]

/-- The closed form `9 * R n + 1 = 10 ^ n`. -/
lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : repunit (n + 1) = repunit n + 10 ^ n := by
        simp [repunit_add n 1]
      rw [h, pow_succ]
      omega

/-- Repunits grow at least as fast as their index. -/
lemma le_repunit (n : ℕ) : n ≤ repunit n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : repunit (n + 1) = repunit n + 10 ^ n := by
        simp [repunit_add n 1]
      have h10 : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega

lemma repunit_strictMono : StrictMono repunit := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : repunit (n + 1) = repunit n + 10 ^ n := by
    simp [repunit_add n 1]
  have h10 : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- If `m ∣ n` then `R m ∣ R n`. -/
lemma repunit_dvd_repunit {m n : ℕ} (h : m ∣ n) : repunit m ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
      have hmul : m * (k + 1) = m * k + m := by ring
      rw [hmul, repunit_add]
      exact Dvd.dvd.add ih (Dvd.dvd.mul_left dvd_rfl _)

/-- **Unconditional partial result.** If the repunit `R n` is prime, then `n` is prime. -/
theorem prime_of_repunit_prime {n : ℕ} (hp : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [repunit_zero] at hp
    exact Nat.not_prime_zero hp
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [repunit_one] at hp
    exact Nat.not_prime_one hp
  rw [Nat.prime_def]
  refine ⟨by omega, ?_⟩
  intro d hd
  by_contra hcon
  push_neg at hcon
  obtain ⟨hd1, hdn⟩ := hcon
  have hdvd : repunit d ∣ repunit n := repunit_dvd_repunit hd
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) hd
  have hdlt : d < n := lt_of_le_of_ne hdle hdn
  have h2 : 2 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [Nat.zero_dvd] at hd; omega
    · omega
  have hlt : repunit d < repunit n := repunit_strictMono hdlt
  have hone : repunit d ≠ 1 := by
    have h11 : repunit 2 ≤ repunit d := repunit_strictMono.monotone h2
    rw [repunit_two] at h11
    omega
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact hone h
  · omega

/-- The set of repunit primes. -/
def repunitPrimes : Set ℕ := {p | p.Prime ∧ ∃ n, p = repunit n}

/-- The repunit prime `R 2 = 11`; in particular `repunitPrimes` is nonempty. -/
theorem eleven_mem_repunitPrimes : 11 ∈ repunitPrimes :=
  ⟨by norm_num, ⟨2, repunit_two.symm⟩⟩

/--
**Conditional reduction of the repunit-prime infinitude conjecture.**

Assuming the (open) hypothesis that repunit primes occur with arbitrarily large index,
the set of repunit primes is infinite.

By `prime_of_repunit_prime` such indices are necessarily prime, so the hypothesis says
exactly that there are infinitely many primes `n` for which the `n`-digit repunit is prime.
-/
theorem RepunitPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n)) :
    repunitPrimes.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hp⟩ := h a
  refine ⟨repunit n, ⟨hp, ⟨n, rfl⟩⟩, ?_⟩
  have := le_repunit n
  omega

/--
**The repunit-prime infinitude conjecture is equivalent to its index form.**

The set of repunit primes is infinite if and only if repunit primes occur at
arbitrarily large indices.  This makes the hypothesis of `RepunitPrimeInfinitude`
not merely sufficient but exactly equivalent to the conclusion.
-/
theorem repunitPrimes_infinite_iff :
    repunitPrimes.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n) := by
  refine ⟨fun hinf N => ?_, RepunitPrimeInfinitude⟩
  obtain ⟨p, hp, hgt⟩ := hinf.exists_gt (repunit N)
  obtain ⟨hprime, n, rfl⟩ := hp
  exact ⟨n, repunit_strictMono.lt_iff_lt.mp hgt, hprime⟩

end Brockian.RepunitPrimes

