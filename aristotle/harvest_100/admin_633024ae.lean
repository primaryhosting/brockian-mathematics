/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is written as a
-- plain block comment; the identical text is repeated as a module docstring below.)

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- Trial divisors: all primes below `41`.  A number `m < 41 ^ 2 = 1681` is prime iff it is
at least `2` and is not divisible by any of these (other than possibly being one of them). -/
def trialDivisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- Boolean primality test, correct for inputs below `1681`. -/
def isPrimeB (m : ℕ) : Bool :=
  decide (2 ≤ m) && trialDivisors.all (fun d => d == m || !(m % d == 0))

/-- The primes used as the small summand in the Goldbach decompositions of the wheel. -/
def wheelPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- Boolean check that `n` is the sum of a prime from `wheelPrimes` and another prime. -/
def gbCheck (n : ℕ) : Bool :=
  wheelPrimes.any (fun p => decide (p ≤ n) && isPrimeB p && isPrimeB (n - p))

/-- Correctness of the boolean primality test below `1681`. -/
theorem isPrimeB_spec {m : ℕ} (hm : m < 1681) (h : isPrimeB m = true) : Nat.Prime m := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hp
  have hm1 : m ≠ 1 := by omega
  have hf : Nat.Prime (Nat.minFac m) := Nat.minFac_prime hm1
  have hdvd : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have hsq : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hp
  have h41 : Nat.minFac m < 41 := by nlinarith [hf.two_le]
  have hmem : Nat.minFac m ∈ trialDivisors := by
    have h2' : 2 ≤ Nat.minFac m := hf.two_le
    rw [trialDivisors]
    interval_cases h : (Nat.minFac m) <;> revert hf <;> decide
  have := hall _ hmem
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    Nat.dvd_iff_mod_eq_zero.symm] at this
  rcases this with heq | hnd
  · exact hp (heq ▸ hf)
  · exact hnd hdvd

/-- If the boolean Goldbach check succeeds on `n < 1681`, then `n` is a sum of two primes. -/
theorem gbCheck_spec {n : ℕ} (hn : n < 1681) (h : gbCheck n = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  rw [gbCheck, List.any_eq_true] at h
  obtain ⟨p, hp, hcond⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨⟨hple, hpp⟩, hqp⟩ := hcond
  have hpb : p < 1681 := by
    have : ∀ x ∈ wheelPrimes, x < 1681 := by decide
    exact this p hp
  refine ⟨p, n - p, isPrimeB_spec hpb hpp, isPrimeB_spec (by omega) hqp, by omega⟩

/-- The finite verification underlying the wheel: the boolean Goldbach check succeeds for
every even number between `4` and `1456`. -/
theorem gbCheck_all : ((List.range 729).all (fun k => decide (k < 2) || gbCheck (2 * k))) = true := by
  decide

/-- **Key intermediate lemma.**  Every even number `n` with `4 ≤ n ≤ 1456` is a sum of two
primes. -/
theorem goldbach_even_le_1456 {n : ℕ} (hev : Even n) (h4 : 4 ≤ n) (hle : n ≤ 1456) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨k, hk⟩ := hev
  have hk' : n = 2 * k := by omega
  have hkr : k ∈ List.range 729 := by
    rw [List.mem_range]; omega
  have := (List.all_eq_true.1 gbCheck_all) k hkr
  rw [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · omega
  · rw [hk']
    exact gbCheck_spec (by omega) h

/-- **Goldbach wheel of modulus 727, `K = 2`.**  Every residue class modulo `727` is
represented by a sum of two primes. -/
theorem GoldbachWheelK2_727 :
    ∀ r : ZMod 727, ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ (p : ZMod 727) + (q : ZMod 727) = r := by
  intro r
  set v : ℕ := r.val with hv
  have hvlt : v < 727 := ZMod.val_lt r
  have hvr : (v : ZMod 727) = r := by
    simp [hv, ZMod.natCast_val, ZMod.cast_id]
  -- choose an even representative `n` of `r` in the range `[4, 1456]`
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ :
      ∃ n : ℕ, Even n ∧ 4 ≤ n ∧ n ≤ 1456 ∧ (n : ZMod 727) = r := by
    rcases Nat.even_or_odd v with he | ho
    · rcases lt_or_ge v 4 with hlt | hge
      · obtain ⟨t, ht⟩ := he
        refine ⟨v + 1454, ⟨t + 727, by omega⟩, by omega, by omega, ?_⟩
        · have h1454 : ((1454 : ℕ) : ZMod 727) = 0 := by decide
          rw [Nat.cast_add, hvr, h1454, add_zero]
      · exact ⟨v, he, hge, by omega, hvr⟩
    · refine ⟨v + 727, ?_, by omega, by omega, ?_⟩
      · rcases ho with ⟨t, ht⟩; exact ⟨t + 364, by omega⟩
      · have h727 : ((727 : ℕ) : ZMod 727) = 0 := by decide
        rw [Nat.cast_add, hvr, h727, add_zero]
  obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_even_le_1456 hn1 hn2 hn3
  refine ⟨p, q, hp, hq, ?_⟩
  rw [← hn4, ← hpq]
  push_cast
  ring

end Brockian

