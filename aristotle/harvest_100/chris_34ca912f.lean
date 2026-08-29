/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file: Lean 4 requires
`import` commands to precede any module docstring.)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The wheel modulus considered here. -/
def wheelModulus : ℕ := 727

/-- The trial-division basis: all primes `< 41`.  Since `41 ^ 2 = 1681`, testing
divisibility by these primes decides primality for every `n ≤ 1680`. -/
def trialBasis : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- Boolean primality test by trial division against `trialBasis`; correct for `n ≤ 1680`. -/
def isPrimeB (n : ℕ) : Bool := 2 ≤ n && trialBasis.all (fun d => n % d != 0 || n == d)

/-- The candidate small primes used as the first summand of a Goldbach pair. -/
def wheelCandidates : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]

/-- Boolean Goldbach test: is `n` the sum of a candidate small prime and another prime? -/
def goldbachB (n : ℕ) : Bool :=
  wheelCandidates.any (fun p => isPrimeB p && isPrimeB (n - p) && p ≤ n)

/-- `n` is a sum of two primes. -/
def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Every prime whose square is at most `1680` belongs to `trialBasis`. -/
lemma mem_trialBasis_of_prime {m : ℕ} (hm : m.Prime) (h : m * m ≤ 1680) :
    m ∈ trialBasis := by
  have h2 := hm.two_le
  have hm40 : m ≤ 40 := by nlinarith
  interval_cases m <;> first | (exact absurd hm (by decide)) | decide

/-- Correctness of the boolean primality test in the intended range. -/
lemma prime_of_isPrimeB {n : ℕ} (hn : n ≤ 1680) (h : isPrimeB n = true) : n.Prime := by
  have h2 : 2 ≤ n := by
    have := (Bool.and_eq_true_iff.mp h).1
    simpa using this
  by_contra hnp
  have hcomp : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hmp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hm2 := hmp.two_le
  have hsq : n.minFac * n.minFac ≤ n := by nlinarith [hcomp]
  have hmem : n.minFac ∈ trialBasis := mem_trialBasis_of_prime hmp (by omega)
  have hall := (Bool.and_eq_true_iff.mp h).2
  have hx := List.all_eq_true.mp hall _ hmem
  have hdvd : n % n.minFac = 0 := Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n)
  simp [hdvd] at hx
  have : n.minFac < n := by nlinarith
  omega

/-- From a successful boolean Goldbach test we get an actual pair of primes. -/
lemma isSumOfTwoPrimes_of_goldbachB {n : ℕ} (hn : n ≤ 1680) (h : goldbachB n = true) :
    IsSumOfTwoPrimes n := by
  obtain ⟨p, hp, hcheck⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcheck
  exact ⟨p, n - p, prime_of_isPrimeB (by omega) h1, prime_of_isPrimeB (by omega) h2, by omega⟩

/-- The finite verification: every even `n` with `4 ≤ n ≤ 2 * 727 + 2` passes the test. -/
lemma goldbachB_all : ∀ n < 1457, 4 ≤ n → n % 2 = 0 → goldbachB n = true := by decide

/-- Wheel witness: for a residue `r < 727`, an even number in the verified range whose
residue modulo `727` is `r`. -/
def wheelWitness (r : ℕ) : ℕ :=
  if r = 0 then 1454 else if r = 2 then 1456 else if r % 2 = 0 then r else r + 727

lemma wheelWitness_spec : ∀ r < 727,
    4 ≤ wheelWitness r ∧ wheelWitness r ≤ 1456 ∧ wheelWitness r % 2 = 0 ∧
      wheelWitness r % 727 = r := by decide

/-- **Goldbach wheel, `K = 2`, modulus `727`.**
Every even number `n` with `4 ≤ n ≤ 2 * 727 + 2` is a sum of two primes, and moreover every
residue class modulo the wheel modulus `727` is represented by such an `n`. -/
theorem GoldbachWheelK2_727 :
    (∀ n : ℕ, 4 ≤ n → n ≤ 2 * wheelModulus + 2 → Even n → IsSumOfTwoPrimes n) ∧
    (∀ r < wheelModulus, ∃ n : ℕ, 4 ≤ n ∧ n ≤ 2 * wheelModulus + 2 ∧ Even n ∧
      n % wheelModulus = r ∧ IsSumOfTwoPrimes n) := by
  have main : ∀ n : ℕ, 4 ≤ n → n ≤ 1456 → n % 2 = 0 → IsSumOfTwoPrimes n := by
    intro n h4 hle heven
    exact isSumOfTwoPrimes_of_goldbachB (by omega) (goldbachB_all n (by omega) h4 heven)
  constructor
  · intro n h4 hle heven
    have : n % 2 = 0 := Nat.even_iff.mp heven
    exact main n h4 (by simpa [wheelModulus] using hle) this
  · intro r hr
    obtain ⟨h4, hle, hpar, hmod⟩ := wheelWitness_spec r (by simpa [wheelModulus] using hr)
    exact ⟨wheelWitness r, h4, by simpa [wheelModulus] using hle, Nat.even_iff.mpr hpar,
      by simpa [wheelModulus] using hmod, main _ h4 hle hpar⟩

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

