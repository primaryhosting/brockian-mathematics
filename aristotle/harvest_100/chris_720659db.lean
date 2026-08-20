/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The wheel modulus of this member of the `GoldbachWheelK2` family. -/
def wheelModulus : Nat := 1051

/-- Primality of a natural number, spelled out by trial division:
`n` is at least `2` and no `m` with `2 ≤ m < n` divides `n`. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m < n → 2 ≤ m → n % m ≠ 0

/-- A boolean trial-division test, used to make `IsPrimeNat` efficiently decidable. -/
def primeCheck (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun m => decide (m < 2) || decide (n % m ≠ 0))

theorem primeCheck_iff (n : Nat) : primeCheck n = true ↔ IsPrimeNat n := by
  simp only [primeCheck, IsPrimeNat, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hm2 => ?_⟩
    rcases h m hm with h' | h'
    · omega
    · simpa using h'
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm => ?_⟩
    by_cases hm2 : 2 ≤ m
    · exact Or.inr (by simpa using h m hm hm2)
    · exact Or.inl (by omega)

instance : DecidablePred IsPrimeNat := fun n => decidable_of_iff _ (primeCheck_iff n)

/-- The wheel: all primes up to the wheel modulus `1051`. -/
def wheelPrimes : List Nat :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,
   127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,
   251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,
   389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,
   541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,
   677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,
   839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,
   1009,1013,1019,1021,1031,1033,1039,1049,1051]

/-- Every entry of the wheel is prime. -/
theorem wheelPrimes_prime : ∀ p ∈ wheelPrimes, IsPrimeNat p := by decide

/-- The arithmetical core of the Goldbach verification: for every `k < 524`,
the even number `2 * k + 4` is a sum of two entries of the wheel. -/
theorem wheel_pair_core :
    ∀ k ∈ List.range 524, ∃ p ∈ wheelPrimes, ∃ q ∈ wheelPrimes, p + q = 2 * k + 4 := by decide

/-- Goldbach's binary conjecture, verified for every even number up to the wheel
modulus `1051`. -/
theorem goldbach_le_1051 (n : Nat) (hev : n % 2 = 0) (h4 : 4 ≤ n) (hle : n ≤ 1051) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  obtain ⟨k, hk, hkn⟩ : ∃ k, k < 524 ∧ n = 2 * k + 4 := ⟨(n - 4) / 2, by omega, by omega⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := wheel_pair_core k (List.mem_range.mpr hk)
  exact ⟨p, q, wheelPrimes_prime p hp, wheelPrimes_prime q hq, by omega⟩

/-- Any nonzero residue below the (prime) wheel modulus is coprime to it. -/
theorem gcd_1051_eq_one (b : Nat) (hb : 0 < b) (hlt : b < 1051) : Nat.gcd b 1051 = 1 := by
  have hprime : IsPrimeNat 1051 := by decide
  have hdvd : Nat.gcd b 1051 ∣ 1051 := Nat.gcd_dvd_right _ _
  have hdb : Nat.gcd b 1051 ∣ b := Nat.gcd_dvd_left _ _
  have hdle : Nat.gcd b 1051 ≤ b := Nat.le_of_dvd hb hdb
  have hdlt : Nat.gcd b 1051 < 1051 := Nat.lt_of_le_of_lt hdle hlt
  by_cases h2 : 2 ≤ Nat.gcd b 1051
  · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) (hprime.2 _ hdlt h2)
  · have hd0 : Nat.gcd b 1051 ≠ 0 := by
      intro h
      rw [h] at hdvd
      exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by decide)
    omega

/-- The `K = 2` wheel-covering condition at the modulus `1051`: every residue class
modulo `1051` is the sum of two residues that are nonzero and coprime to `1051`. -/
theorem wheel_two_units_cover (r : Nat) (hr : r < 1051) :
    ∃ a b : Nat, 0 < a ∧ a < 1051 ∧ 0 < b ∧ b < 1051 ∧
      Nat.gcd a 1051 = 1 ∧ Nat.gcd b 1051 = 1 ∧ (a + b) % 1051 = r := by
  by_cases h0 : r = 0
  · subst h0
    exact ⟨1, 1050, by omega, by omega, by omega, by omega,
      gcd_1051_eq_one 1 (by omega) (by omega),
      gcd_1051_eq_one 1050 (by omega) (by omega), by omega⟩
  by_cases h1 : r = 1
  · subst h1
    exact ⟨2, 1050, by omega, by omega, by omega, by omega,
      gcd_1051_eq_one 2 (by omega) (by omega),
      gcd_1051_eq_one 1050 (by omega) (by omega), by omega⟩
  exact ⟨1, r - 1, by omega, by omega, by omega, by omega,
    gcd_1051_eq_one 1 (by omega) (by omega),
    gcd_1051_eq_one (r - 1) (by omega) (by omega), by omega⟩

/-- **Goldbach Wheel K 2, modulus 1051.**
The wheel modulus `1051` is prime; Goldbach's binary conjecture holds for every even
number up to `1051`, with both summands drawn from the wheel of primes below the
modulus; and every residue class modulo `1051` is a sum of two residues coprime to
`1051` (the `K = 2` wheel-covering condition). -/
theorem GoldbachWheelK2_1051 :
    IsPrimeNat wheelModulus ∧
    (∀ n : Nat, n % 2 = 0 → 4 ≤ n → n ≤ wheelModulus →
      ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n) ∧
    (∀ r : Nat, r < wheelModulus →
      ∃ a b : Nat, 0 < a ∧ a < wheelModulus ∧ 0 < b ∧ b < wheelModulus ∧
        Nat.gcd a wheelModulus = 1 ∧ Nat.gcd b wheelModulus = 1 ∧
        (a + b) % wheelModulus = r) :=
  ⟨by decide, goldbach_le_1051, wheel_two_units_cover⟩

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

import Mathlib
import RequestProject.GoldbachWheelK2_1051

/-!
# Mathlib restatement of `Brockian.GoldbachWheelK2_1051`

The file `RequestProject/GoldbachWheelK2_1051.lean` is Mathlib-free (its mandated
header comment must be the very first thing in the file, and Lean does not allow
`import` after a module docstring).  It therefore uses the self-contained
trial-division predicate `Brockian.IsPrimeNat`.

Here we check that `Brockian.IsPrimeNat` really is primality in Mathlib's sense,
and restate the main results using `Nat.Prime` and `Nat.Coprime`.
-/

namespace Brockian

/-- The trial-division predicate used in the Mathlib-free file agrees with `Nat.Prime`. -/
theorem isPrimeNat_iff_natPrime (n : ℕ) : IsPrimeNat n ↔ Nat.Prime n := by
  rw [Nat.prime_def_lt]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · simp at hdvd; omega
      · rfl
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) (h m hm hge)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hge hmod => ?_⟩
    have : m ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have := h m hm this
    omega

/-- Goldbach's binary conjecture (Mathlib's `Nat.Prime`), verified for every even
number up to the wheel modulus `1051`. -/
theorem goldbach_le_1051_natPrime (n : ℕ) (hev : Even n) (h4 : 4 ≤ n) (hle : n ≤ wheelModulus) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  have hmod : n % 2 = 0 := Nat.even_iff.mp hev
  obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_le_1051 n hmod h4 hle
  exact ⟨p, q, (isPrimeNat_iff_natPrime p).mp hp, (isPrimeNat_iff_natPrime q).mp hq, hpq⟩

/-- The `K = 2` wheel-covering condition, phrased with `Nat.Coprime`: every residue
class modulo the wheel modulus `1051` is a sum of two residues coprime to it. -/
theorem wheel_two_units_cover_coprime (r : ℕ) (hr : r < wheelModulus) :
    ∃ a b : ℕ, 0 < a ∧ a < wheelModulus ∧ 0 < b ∧ b < wheelModulus ∧
      Nat.Coprime a wheelModulus ∧ Nat.Coprime b wheelModulus ∧
      (a + b) % wheelModulus = r :=
  wheel_two_units_cover r hr

end Brockian

