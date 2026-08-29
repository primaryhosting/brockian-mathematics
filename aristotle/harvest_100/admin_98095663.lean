/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file establishes a new member of the `GoldbachWheelK2` family: the binary
(`K = 2`) Goldbach property for the wheel modulus `947`, i.e. every even number
`n` with `4 ≤ n ≤ 2 * 947` is a sum of two primes `p + q` with `p ≤ q`.

The proof is a kernel-checked finite verification.  A trial-division primality
test `Brockian.isPrimeB`, sound for inputs below `44 ^ 2 = 1936`
(`Brockian.isPrimeB_prime`, via `Nat.prime_def_le_sqrt`), is combined with a
`decide`-checked search of a fixed wheel of small prime candidates.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Brockian

/-- `noDivUpto n b = true` says that no `k` with `2 ≤ k ≤ b` and `k ≠ n` divides `n`. -/
def noDivUpto (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | (k + 2) => ((n % (k + 2) != 0) || (n == k + 2)) && noDivUpto n (k + 1)

lemma noDivUpto_not_dvd :
    ∀ (b n k : ℕ), noDivUpto n b = true → 2 ≤ k → k ≤ b → k ≠ n → ¬ k ∣ n := by
  intro b
  induction b with
  | zero => intro n k _ hk hkb; omega
  | succ b ih =>
    match b with
    | 0 => intro n k _ hk hkb; omega
    | (b + 1) =>
      intro n k h hk hkb hkn
      rw [noDivUpto, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.lt_or_ge k (b + 2) with hlt | hge
      · exact ih n k h2 hk (by omega) hkn
      · have hkeq : k = b + 2 := by omega
        subst hkeq
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h1
        rcases h1 with h1 | h1
        · exact fun hdvd => h1 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact absurd h1.symm hkn

/-- Trial-division primality test, sound for inputs `< 1936 = 44 ^ 2`. -/
def isPrimeB (n : ℕ) : Bool := (2 ≤ n) && noDivUpto n 43

lemma isPrimeB_prime {n : ℕ} (hn : n < 1936) (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms => ?_⟩
  have hs : n.sqrt ≤ 43 := by
    have h44 : n.sqrt < 44 := Nat.sqrt_lt'.2 (by norm_num; omega)
    omega
  have hmn : m ≠ n := by
    have := Nat.sqrt_lt_self (show 1 < n by omega)
    omega
  exact noDivUpto_not_dvd 43 n m hd hm (le_trans hms hs) hmn

/-- The wheel of small prime candidates used as the smaller summand. -/
def wheelCands : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199]

lemma wheelCands_lt : ∀ p ∈ wheelCands, p < 1936 := by decide

/-- `goldbachOK n = true` witnesses `n = p + (n - p)` for a wheel prime `p ≤ n / 2`
with `n - p` prime. -/
def goldbachOK (n : ℕ) : Bool :=
  wheelCands.any (fun p => (2 * p ≤ n) && isPrimeB p && isPrimeB (n - p))

/-- The finite kernel check: every even `n` with `4 ≤ n ≤ 1894` passes `goldbachOK`. -/
lemma goldbachOK_check :
    (List.range' 4 1891).all (fun n => (n % 2 == 1) || goldbachOK n) = true := by decide

/-- **Goldbach wheel, `K = 2`, modulus `947`.**  Every even `n` with `4 ≤ n ≤ 2 * 947`
is a sum of two primes `p + q` with `p ≤ q`. -/
theorem GoldbachWheelK2_947 (n : ℕ) (hn : Even n) (h4 : 4 ≤ n) (hub : n ≤ 2 * 947) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ p + q = n := by
  have hmem : n ∈ List.range' 4 1891 := by
    rw [List.mem_range'_1]
    omega
  have h := List.all_eq_true.1 goldbachOK_check n hmem
  have hpar : n % 2 = 0 := Nat.even_iff.1 hn
  have hok : goldbachOK n = true := by
    simpa [hpar] using h
  obtain ⟨p, hp, hpq⟩ := List.any_eq_true.1 hok
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpq
  obtain ⟨⟨hle, hpp⟩, hqq⟩ := hpq
  refine ⟨p, n - p, isPrimeB_prime (wheelCands_lt p hp) hpp,
    isPrimeB_prime (by omega) hqq, by omega, by omega⟩

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

