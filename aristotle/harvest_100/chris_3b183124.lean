/-
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace Brockian

/-- `noFactorBelow n k` is `true` exactly when no `d` with `2 ≤ d ≤ k` divides `n`. -/
def noFactorBelow (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | (k + 2) => (n % (k + 2) != 0) && noFactorBelow n (k + 1)

/-- A trial-division primality test, correct for `n < 2704 = 52 ^ 2`. -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && noFactorBelow n (min 51 (n - 1))

/-- The Goldbach wheel: the small primes used as the first summand. -/
def wheelPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103]

/-- `n` has a Goldbach decomposition whose small summand lies on the wheel. -/
def goldbachB (n : ℕ) : Bool := wheelPrimes.any (fun p => isPrimeB p && isPrimeB (n - p))

/-- The wheel check for every even number in `[4, 2 * 1327]`. -/
def allGoldbach : Bool := (List.range 1326).all (fun k => goldbachB (4 + 2 * k))

theorem not_dvd_of_noFactorBelow :
    ∀ (k n d : ℕ), noFactorBelow n k = true → 2 ≤ d → d ≤ k → ¬ d ∣ n := by
  intro k
  induction k with
  | zero => intro n d _ hd hle; omega
  | succ k ih =>
    match k with
    | 0 => intro n d _ hd hle; omega
    | (k + 1) =>
      intro n d h hd hle
      rw [noFactorBelow, Bool.and_eq_true, bne_iff_ne] at h
      obtain ⟨h1, h2⟩ := h
      rcases eq_or_lt_of_le hle with rfl | hlt
      · intro hdvd
        exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih n d h2 hd (by omega)

theorem prime_of_isPrimeB {n : ℕ} (hn : n < 2704) (h : isPrimeB n = true) : n.Prime := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨h2, hnf⟩ := h
  by_contra hp
  have hd : n.minFac ∣ n := Nat.minFac_dvd n
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hp
  have hmin2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  have hsq' : n.minFac * n.minFac ≤ n := by nlinarith
  have h51 : n.minFac ≤ 51 := by nlinarith
  have hlin : 2 * n.minFac ≤ n.minFac * n.minFac := Nat.mul_le_mul_right _ hmin2
  exact not_dvd_of_noFactorBelow _ _ _ hnf hmin2 (le_min h51 (by omega)) hd

/-- **Goldbach, binary (`K = 2`), verified on the wheel of modulus 1327.**
Every even `n` with `4 ≤ n ≤ 2 * 1327` is a sum of two primes, and the smaller
summand may always be taken from the wheel of primes up to `103`. -/
theorem GoldbachWheelK2_1327 (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 2 * 1327) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 103 ∧ p + q = n := by
  obtain ⟨r, hr⟩ := he
  have hall : allGoldbach = true := by decide
  rw [allGoldbach, List.all_eq_true] at hall
  have hk := hall (r - 2) (List.mem_range.mpr (by omega))
  rw [show 4 + 2 * (r - 2) = n by omega, goldbachB, List.any_eq_true] at hk
  obtain ⟨p, hpmem, hp⟩ := hk
  rw [Bool.and_eq_true] at hp
  have hbound : ∀ p ∈ wheelPrimes, p ≤ 103 := by decide
  have hp103 : p ≤ 103 := hbound p hpmem
  have hpp : p.Prime := prime_of_isPrimeB (by omega) hp.1
  have hqq : (n - p).Prime := prime_of_isPrimeB (by omega) hp.2
  have h2 : 2 ≤ n - p := hqq.two_le
  exact ⟨p, n - p, hpp, hqq, hp103, by omega⟩

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

