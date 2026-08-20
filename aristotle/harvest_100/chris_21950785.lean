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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Erdős–Straus conjecture states that for every `n ≥ 2` the fraction `4 / n` is the sum of
three unit fractions.  It is an open problem, so what is proved here are unconditional partial
results together with a reduction of the full conjecture to a thin family of primes:

* `rep_of_dvd`                : a representation for a divisor of `n` gives one for `n`;
* `rep_of_mod_four_eq_three`  : `n ≡ 3 [MOD 4]` is representable;
* `rep_of_mod_three_eq_two`   : `n ≡ 2 [MOD 3]` is representable;
* `rep_of_mod_twentyFour_eq_thirteen` : `n ≡ 13 [MOD 24]` is representable;
* `rep_of_mod_twentyFour_ne_one` : every `n ≥ 2` with `n % 24 ≠ 1` is representable;
* `erdosStrausConjecture_iff_prime_one_mod_twentyFour` : the conjecture is equivalent to its
  restriction to the primes `p ≡ 1 [MOD 24]`;
* `rep_of_le_1000` : the conjecture holds for all `2 ≤ n ≤ 1000`.

No Mathlib lemma proves the conjecture itself; the search of Mathlib turned up no statement about
Egyptian fraction representations of `4 / n`.
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausRep n` says that `4 / n` can be written as a sum of three unit fractions
with positive natural number denominators (repetitions allowed). -/
def ErdosStrausRep (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The Erdős–Straus conjecture: for every `n ≥ 2` the fraction `4 / n` is a sum of three
unit fractions. -/
def ErdosStrausConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ErdosStrausRep n

/-- A representation for a divisor `d` of `n` yields one for `n`. -/
theorem rep_of_dvd {d n : ℕ} (hdn : d ∣ n) (hn : 0 < n) (hd : ErdosStrausRep d) :
    ErdosStrausRep n := by
  obtain ⟨m, rfl⟩ := hdn
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := hd
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hn
    · exact h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hn
    · exact h
  refine ⟨m * x, m * y, m * z, by positivity, by positivity, by positivity, ?_⟩
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  have hxq : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have key : (4 : ℚ) / ((d : ℚ) * m) = ((4 : ℚ) / d) * (1 / m) := by field_simp
  push_cast
  rw [key, h]
  field_simp

/-- `4/2 = 1/1 + 1/2 + 1/2`. -/
theorem rep_two : ErdosStrausRep 2 :=
  ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `4/3 = 1/1 + 1/6 + 1/6`. -/
theorem rep_three : ErdosStrausRep 3 :=
  ⟨1, 6, 6, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- If `n = 4k + 3` then `4/n = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1))`. -/
theorem rep_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : ErdosStrausRep n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine ⟨k + 1, 2 * (4 * k + 3) * (k + 1), 2 * (4 * k + 3) * (k + 1), by omega, by positivity,
    by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- If `n = 3k + 2` then `4/n = 1/n + 1/(k+1) + 1/(n(k+1))`. -/
theorem rep_of_mod_three_eq_two {n : ℕ} (h : n % 3 = 2) : ErdosStrausRep n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨3 * k + 2, k + 1, (3 * k + 2) * (k + 1), by omega, by omega, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- If `n = 24m + 13` then
`4/n = 1/(6m+4) + 1/(2(24m²+29m+9)) + 1/((144m²+174m+52)(24m²+29m+9))`.

This comes from `4/n - 1/((n+3)/4) = 3/(n(n+3)/4)`, where the remaining fraction `3/M` has
`M ≡ 1 [MOD 3]` and `M` even, so `3/M = 1/(k+1) + 2/(M(k+1))` with `k = (M-1)/3` and
`M(k+1)` even. -/
theorem rep_of_mod_twentyFour_eq_thirteen {n : ℕ} (h : n % 24 = 13) : ErdosStrausRep n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 24 * m + 13 := ⟨n / 24, by omega⟩
  refine ⟨6 * m + 4, 2 * (24 * m ^ 2 + 29 * m + 9),
    (144 * m ^ 2 + 174 * m + 52) * (24 * m ^ 2 + 29 * m + 9), by omega, by positivity,
    by positivity, ?_⟩
  have h1 : (6 * (m : ℚ) + 4) ≠ 0 := by positivity
  have h2 : (24 * (m : ℚ) ^ 2 + 29 * m + 9) ≠ 0 := by positivity
  have h3 : (144 * (m : ℚ) ^ 2 + 174 * m + 52) ≠ 0 := by positivity
  have h4 : (24 * (m : ℚ) + 13) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Unconditional partial result**: the conjecture holds for every `n ≥ 2` with `n % 24 ≠ 1`. -/
theorem rep_of_mod_twentyFour_ne_one {n : ℕ} (h2 : 2 ≤ n) (h : n % 24 ≠ 1) : ErdosStrausRep n := by
  rcases Nat.even_or_odd n with he | ho
  · exact rep_of_dvd he.two_dvd (by omega) rep_two
  · by_cases h3 : 3 ∣ n
    · exact rep_of_dvd h3 (by omega) rep_three
    · have hodd : n % 2 = 1 := Nat.odd_iff.mp ho
      have h3' : n % 3 ≠ 0 := fun hh => h3 (Nat.dvd_of_mod_eq_zero hh)
      have hsplit : n % 4 = 3 ∨ n % 3 = 2 ∨ n % 24 = 13 := by omega
      rcases hsplit with h4 | h4 | h4
      · exact rep_of_mod_four_eq_three h4
      · exact rep_of_mod_three_eq_two h4
      · exact rep_of_mod_twentyFour_eq_thirteen h4

/-- The conjecture holds for every `n ≥ 2` with `n % 12 ≠ 1`. -/
theorem rep_of_mod_twelve_ne_one {n : ℕ} (h2 : 2 ≤ n) (h : n % 12 ≠ 1) : ErdosStrausRep n :=
  rep_of_mod_twentyFour_ne_one h2 (by omega)

/-- A divisor `d ≥ 2` of `n` with `d % 24 ≠ 1` gives a representation for `n`. -/
theorem rep_of_dvd_mod_twentyFour_ne_one {d n : ℕ} (hd2 : 2 ≤ d) (hdn : d ∣ n) (hn : 0 < n)
    (hd : d % 24 ≠ 1) : ErdosStrausRep n :=
  rep_of_dvd hdn hn (rep_of_mod_twentyFour_ne_one hd2 hd)

/-- **Reduction**: the Erdős–Straus conjecture is equivalent to its restriction to the primes
`p ≡ 1 [MOD 24]`. -/
theorem erdosStrausConjecture_iff_prime_one_mod_twentyFour :
    ErdosStrausConjecture ↔ ∀ p : ℕ, p.Prime → p % 24 = 1 → ErdosStrausRep p := by
  constructor
  · intro h p hp _
    exact h p hp.two_le
  · intro h n hn
    by_cases h1 : n % 24 = 1
    · have hpp : (n.minFac).Prime := Nat.minFac_prime (by omega)
      have hpd : n.minFac ∣ n := Nat.minFac_dvd n
      by_cases h24 : n.minFac % 24 = 1
      · exact rep_of_dvd hpd (by omega) (h _ hpp h24)
      · exact rep_of_dvd hpd (by omega) (rep_of_mod_twentyFour_ne_one hpp.two_le h24)
    · exact rep_of_mod_twentyFour_ne_one hn h1

section Explicit

/-! ### Explicit representations for the primes `p ≡ 1 [MOD 24]` below `1000`

By `rep_of_mod_twentyFour_ne_one` these are the only numbers below `1000` that need an
individual treatment. -/

theorem rep_73 : ErdosStrausRep 73 :=
  ⟨20, 210, 30660, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_97 : ErdosStrausRep 97 :=
  ⟨25, 810, 392850, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_193 : ErdosStrausRep 193 :=
  ⟨50, 1380, 1331700, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_241 : ErdosStrausRep 241 :=
  ⟨62, 2139, 1030998, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_313 : ErdosStrausRep 313 :=
  ⟨80, 3580, 4482160, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_337 : ErdosStrausRep 337 :=
  ⟨85, 9550, 54711950, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_409 : ErdosStrausRep 409 :=
  ⟨104, 6084, 4976712, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_433 : ErdosStrausRep 433 :=
  ⟨110, 6805, 64824430, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_457 : ErdosStrausRep 457 :=
  ⟨115, 17520, 184152720, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_577 : ErdosStrausRep 577 :=
  ⟨145, 27890, 466683370, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_601 : ErdosStrausRep 601 :=
  ⟨152, 13053, 62758824, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_673 : ErdosStrausRep 673 :=
  ⟨170, 16345, 374006290, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_769 : ErdosStrausRep 769 :=
  ⟨194, 21340, 16410460, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem rep_937 : ErdosStrausRep 937 :=
  ⟨235, 73400, 3232462600, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Explicit

/-- **Unconditional partial result**: the Erdős–Straus conjecture holds for all `2 ≤ n ≤ 1000`. -/
theorem rep_of_le_1000 {n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ 1000) : ErdosStrausRep n := by
  by_cases h1 : n % 24 = 1
  · have hcases : n = 25 ∨ n = 49 ∨ n = 73 ∨ n = 97 ∨ n = 121 ∨ n = 145 ∨ n = 169 ∨ n = 193 ∨ n = 217 ∨ n = 241 ∨ n = 265 ∨ n = 289 ∨ n = 313 ∨ n = 337 ∨ n = 361 ∨ n = 385 ∨ n = 409 ∨ n = 433 ∨ n = 457 ∨ n = 481 ∨ n = 505 ∨ n = 529 ∨ n = 553 ∨ n = 577 ∨ n = 601 ∨ n = 625 ∨ n = 649 ∨ n = 673 ∨ n = 697 ∨ n = 721 ∨ n = 745 ∨ n = 769 ∨ n = 793 ∨ n = 817 ∨ n = 841 ∨ n = 865 ∨ n = 889 ∨ n = 913 ∨ n = 937 ∨ n = 961 ∨ n = 985 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_73
    · exact rep_97
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 11) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 13) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_193
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_241
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 17) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_313
    · exact rep_337
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 19) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_409
    · exact rep_433
    · exact rep_457
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 13) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 23) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_577
    · exact rep_601
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 11) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_673
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 17) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_769
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 13) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 19) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 29) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 11) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_937
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 31) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact rep_of_dvd_mod_twentyFour_ne_one (d := 5) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  · exact rep_of_mod_twentyFour_ne_one h2 h1

end Brockian.ErdosStraus

