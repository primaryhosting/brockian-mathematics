/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`n` is at least `2` and its only divisors are `1` and `n`. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

/-- The spokes of the wheel: all primes below `37`. -/
def wheelSpokes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- A wheel-style primality test: trial division through all primes below `37`.
It is correct for every `n < 37 ^ 2 = 1369`, in particular below the wheel
modulus `1153`. -/
def wheelPrime (n : Nat) : Bool :=
  2 ≤ n && wheelSpokes.all (fun p => n == p || n % p != 0)

/-- Every integer `q` with `2 ≤ q ≤ 36` is divisible by one of the wheel spokes. -/
theorem exists_spoke_dvd : ∀ q ∈ List.range 37, 2 ≤ q → ∃ p ∈ wheelSpokes, p ∣ q := by
  decide

/-- If the wheel test succeeds on `n < 1369`, then `n` has no divisor `q` with
`2 ≤ q ≤ 36` and `q < n`. -/
theorem no_small_divisor {n : Nat} (h : wheelPrime n = true) {q : Nat}
    (hq2 : 2 ≤ q) (hq36 : q ≤ 36) (hqn : q < n) (hqd : q ∣ n) : False := by
  rw [wheelPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  obtain ⟨p, hp, hpq⟩ := exists_spoke_dvd q (List.mem_range.2 (by omega)) hq2
  have hpn : p ∣ n := Nat.dvd_trans hpq hqd
  have hspoke := hall p hp
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hspoke
  have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hpn
  have hnp : n = p := by
    rcases hspoke with h1 | h1
    · exact h1
    · exact absurd hmod h1
  have hpq' : p ≤ q := Nat.le_of_dvd (by omega) hpq
  have hqn' : q ≤ n := Nat.le_of_dvd (by omega) hqd
  omega

/-- Correctness of the wheel test in its range of validity. -/
theorem isPrime_of_wheelPrime {n : Nat} (hn : n < 1369) (h : wheelPrime n = true) :
    IsPrime n := by
  have h2 : 2 ≤ n := by
    rw [wheelPrime, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  refine ⟨h2, ?_⟩
  intro d hd
  apply Classical.byContradiction
  intro hcon
  have hd1 : d ≠ 1 := fun h => hcon (Or.inl h)
  have hdn : d ≠ n := fun h => hcon (Or.inr h)
  obtain ⟨e, he⟩ := hd
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_mul] at he
    omega
  have hd2 : 2 ≤ d := by omega
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) ⟨e, he⟩
  have hdlt : d < n := by omega
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · have hcase : e = 0 ∨ e = 1 := by omega
      rcases hcase with rfl | rfl <;> omega
    · exact hge
  have helt : e < n := by
    have hc : e * d = d * e := Nat.mul_comm e d
    have : e * 2 ≤ e * d := Nat.mul_le_mul_left e hd2
    omega
  rcases Nat.le_total d e with hde | hde
  · have hsq : d * d ≤ n := by
      have : d * d ≤ d * e := Nat.mul_le_mul_left d hde
      omega
    have hd36 : d ≤ 36 := by
      apply Classical.byContradiction
      intro hc
      have : 37 * 37 ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
      omega
    exact no_small_divisor h hd2 hd36 hdlt ⟨e, he⟩
  · have hsq : e * e ≤ n := by
      have : e * e ≤ d * e := Nat.mul_le_mul_right e hde
      omega
    have he36 : e ≤ 36 := by
      apply Classical.byContradiction
      intro hc
      have : 37 * 37 ≤ e * e := Nat.mul_le_mul (by omega) (by omega)
      omega
    exact no_small_divisor h he2 he36 helt ⟨d, by rw [he]; exact Nat.mul_comm d e⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The finite Goldbach computation: for every `m` with `2 ≤ m ≤ 576` — that is, for
every even number `2 * m` between `4` and `1152` — there is a prime `p < 100` such that
both `p` and `2 * m - p` pass the wheel test. -/
theorem goldbach_wheel_data :
    ∀ m ∈ List.range 577, 2 ≤ m →
      ∃ p ∈ List.range 100, wheelPrime p = true ∧ wheelPrime (2 * m - p) = true := by
  decide

/-- **Goldbach's conjecture below the wheel modulus 1153**: every even natural number
`n` with `4 ≤ n ≤ 1153` is a sum of two primes. -/
theorem GoldbachWheelK2_1153 :
    ∀ n : Nat, 4 ≤ n → n ≤ 1153 → n % 2 = 0 →
      ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = n := by
  intro n hn4 hn1153 hne
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  obtain ⟨p, hp, hwp, hwq⟩ :=
    goldbach_wheel_data m (List.mem_range.2 (by omega)) (by omega)
  rw [List.mem_range] at hp
  have hp2 : 2 ≤ p := by
    apply Classical.byContradiction
    intro hc
    have hcase : p = 0 ∨ p = 1 := by omega
    rcases hcase with rfl | rfl
    · exact absurd hwp (by decide)
    · exact absurd hwp (by decide)
  have hle : p ≤ 2 * m := by
    apply Classical.byContradiction
    intro hc
    have hz : 2 * m - p = 0 := by omega
    rw [hz] at hwq
    exact absurd hwq (by decide)
  exact ⟨p, 2 * m - p, isPrime_of_wheelPrime (by omega) hwp,
    isPrime_of_wheelPrime (by omega) hwq, by omega⟩

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_1153

/-!
# Goldbach Wheel K 2 1153 — Mathlib-flavoured restatement

Companion to `RequestProject/GoldbachWheelK2_1153.lean`, which (in order to keep the
required header comment as the very first item in the file) is written against Lean
core only and uses the local predicate `Brockian.IsPrime`.

Here we identify `Brockian.IsPrime` with Mathlib's `Nat.Prime` and restate the main
theorem with `Nat.Prime` and `Even`.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrime_iff_nat_prime {n : ℕ} : IsPrime n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hd⟩
    rw [Nat.prime_def]
    exact ⟨h2, fun d hdvd => (hd d hdvd).imp id id⟩
  · intro hp
    exact ⟨hp.two_le, fun d hdvd => (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd)⟩

/-- **Goldbach's conjecture below the wheel modulus 1153**, stated with Mathlib's
`Nat.Prime` and `Even`: every even natural number `n` with `4 ≤ n ≤ 1153` is a sum of
two primes. -/
theorem goldbachWheelK2_1153_nat_prime :
    ∀ n : ℕ, 4 ≤ n → n ≤ 1153 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n hn4 hn1153 hev
  obtain ⟨k, hk⟩ := hev
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_1153 n hn4 hn1153 (by omega)
  exact ⟨p, q, isPrime_iff_nat_prime.mp hp, isPrime_iff_nat_prime.mp hq, hpq⟩

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

