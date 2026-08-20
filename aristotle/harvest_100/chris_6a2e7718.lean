import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The primes below `41`; a trial-division wheel sufficient to decide primality
below `41 ^ 2 = 1681`. -/
def wheelPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- Fast (kernel-friendly) primality test, correct for arguments `< 1681`. -/
def wheelIsPrime (n : ℕ) : Bool :=
  1 < n && wheelPrimes.all (fun d => decide (n < d * d) || !(n % d == 0))

/-- Boolean Goldbach check: `n` is small, odd, or a sum of two primes. -/
def goldbachCheck (n : ℕ) : Bool :=
  n < 4 || n % 2 == 1 || (List.range n).any (fun p => wheelIsPrime p && wheelIsPrime (n - p))

lemma prime_lt_41_mem_wheelPrimes (d : ℕ) (hd : d < 41) (hp : Nat.Prime d) :
    d ∈ wheelPrimes := by
  revert hp
  revert hd
  revert d
  decide

lemma wheelIsPrime_correct {n : ℕ} (hn : n < 1681) (h : wheelIsPrime n = true) :
    Nat.Prime n := by
  rw [wheelIsPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  by_contra hnp
  set d := n.minFac with hd
  have hdp : Nat.Prime d := Nat.minFac_prime (by omega)
  have hsq : d ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hdlt : d < 41 := by nlinarith [hsq, hdp.two_le]
  have hmem : d ∈ wheelPrimes := prime_lt_41_mem_wheelPrimes d hdlt hdp
  have hdvd : n % d = 0 := Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n)
  have hlt := h2 d hmem
  simp [hdvd] at hlt
  nlinarith [hsq, hlt]

lemma goldbachCheck_all : (List.range 1327).all goldbachCheck = true := by decide

/-- **Goldbach wheel, K = 2, modulus 1327.**
Every even number `n` with `4 ≤ n < 1327` is the sum of two primes. -/
theorem GoldbachWheelK2_1327 :
    ∀ n : ℕ, 4 ≤ n → n < 1327 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n h4 hlt hev
  have h := List.all_eq_true.mp goldbachCheck_all n (List.mem_range.mpr hlt)
  obtain ⟨k, rfl⟩ := hev
  rw [goldbachCheck] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with (h | h) | h
  · omega
  · omega
  · obtain ⟨p, hpm, hp⟩ := List.any_eq_true.mp h
    rw [List.mem_range] at hpm
    rw [Bool.and_eq_true] at hp
    exact ⟨p, k + k - p, wheelIsPrime_correct (by omega) hp.1,
      wheelIsPrime_correct (by omega) hp.2, by omega⟩

end Brockian

