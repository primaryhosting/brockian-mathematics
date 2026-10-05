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
/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` means that `4 / n` can be written as a sum of three unit fractions
with positive (natural) denominators. -/
def Solvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The Erdős–Straus conjecture: for every `n ≥ 2` the fraction `4 / n` is a sum of
three unit fractions. -/
def ErdosStrausConjecture : Prop := ∀ n : ℕ, 2 ≤ n → Solvable n

/-- Splitting a unit fraction into two: `1/m = 1/(m+1) + 1/(m(m+1))`. -/
lemma one_div_split (m : ℕ) (hm : 0 < m) :
    (1 : ℚ) / m = 1 / ((m + 1 : ℕ) : ℚ) + 1 / ((m * (m + 1) : ℕ) : ℚ) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- If `4/n` is a sum of *two* unit fractions, it is a sum of three. -/
lemma solvable_of_pair {n a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : (4 : ℚ) / n = 1 / a + 1 / b) : Solvable n := by
  refine ⟨a, b + 1, b * (b + 1), ha, by positivity, by positivity, ?_⟩
  rw [h, one_div_split b hb]
  ring

/-- If `d ∣ n`, `n > 0` and `4/d` is a sum of three unit fractions, so is `4/n`. -/
lemma Solvable.of_dvd {d n : ℕ} (hn : 0 < n) (hdvd : d ∣ n) (hd : Solvable d) :
    Solvable n := by
  obtain ⟨m, rfl⟩ := hdvd
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := hd
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0] at hn
    · exact h0
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · simp [h0] at hn
    · exact h0
  refine ⟨x * m, y * m, z * m, by positivity, by positivity, by positivity, ?_⟩
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hxq : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hsplit : (4 : ℚ) / ((d * m : ℕ) : ℚ) = ((4 : ℚ) / d) / m := by
    push_cast; field_simp
  rw [hsplit, h]
  push_cast
  field_simp

/-- Even case: `4/(2m) = 1/m + 1/m`. -/
lemma solvable_of_even {n : ℕ} (hn : 0 < n) (h2 : 2 ∣ n) : Solvable n := by
  obtain ⟨m, rfl⟩ := h2
  have hm : 0 < m := by omega
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine solvable_of_pair hm hm ?_
  push_cast
  field_simp
  norm_num

/-- Case `3 ∣ n`: `4/(3m) = 1/m + 1/(3m)`. -/
lemma solvable_of_three_dvd {n : ℕ} (hn : 0 < n) (h3 : 3 ∣ n) : Solvable n := by
  obtain ⟨m, rfl⟩ := h3
  have hm : 0 < m := by omega
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine solvable_of_pair hm (by omega : 0 < 3 * m) ?_
  push_cast
  field_simp
  ring

/-- Case `n ≡ 3 [MOD 4]`: with `n = 4k+3`, `4/n = 1/(k+1) + 1/((k+1)n)`. -/
lemma solvable_of_three_mod_four {n : ℕ} (hn : n % 4 = 3) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine solvable_of_pair (by omega : 0 < k + 1)
    (by positivity : 0 < (k + 1) * (4 * k + 3)) ?_
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hn' : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Case `n ≡ 2 [MOD 3]`: with `n = 3k+2`, `4/n = 1/(k+1) + 1/n + 1/(n(k+1))`. -/
lemma solvable_of_two_mod_three {n : ℕ} (hn : n % 3 = 2) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega, by positivity, ?_⟩
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hn' : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Case `n ≡ 13 [MOD 24]`: with `n = 24t+13`,
`4/n = 1/(6t+4) + 1/(48t²+58t+18) + 1/(2(24t+13)(3t+2)(24t²+29t+9))`.

(This comes from `4/n = 1/x + 3/(nx)` with `x = (n+3)/4`, followed by
`3/m = 1/((m+2)/3) + 1/(m(m+2)/6)`, which is legitimate exactly when `m = nx`
is even and `m ≡ 1 [MOD 3]`.) -/
lemma solvable_of_thirteen_mod_24 {n : ℕ} (hn : n % 24 = 13) : Solvable n := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 24 * t + 13 := ⟨n / 24, by omega⟩
  refine ⟨6 * t + 4, 48 * t ^ 2 + 58 * t + 18,
    2 * (24 * t + 13) * (3 * t + 2) * (24 * t ^ 2 + 29 * t + 9),
    by positivity, by positivity, by positivity, ?_⟩
  have ht : (0:ℚ) ≤ (t:ℚ) := Nat.cast_nonneg t
  have h1 : (24 * (t:ℚ) + 13) ≠ 0 := by positivity
  have h2 : (6 * (t:ℚ) + 4) ≠ 0 := by positivity
  have h3 : (48 * (t:ℚ) ^ 2 + 58 * t + 18) ≠ 0 := by positivity
  have h4 : (3 * (t:ℚ) + 2) ≠ 0 := by positivity
  have h5 : (24 * (t:ℚ) ^ 2 + 29 * t + 9) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The conjecture holds for every `n ≥ 2` with `n % 12 ≠ 1`. -/
theorem solvable_of_mod_twelve_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 12 ≠ 1) : Solvable n := by
  have hn0 : 0 < n := by omega
  by_cases h2 : n % 2 = 0
  · exact solvable_of_even hn0 (Nat.dvd_of_mod_eq_zero h2)
  by_cases h3 : n % 3 = 0
  · exact solvable_of_three_dvd hn0 (Nat.dvd_of_mod_eq_zero h3)
  by_cases h4 : n % 4 = 3
  · exact solvable_of_three_mod_four h4
  exact solvable_of_two_mod_three (by omega)

/-- The conjecture holds for every `n ≥ 2` with `n % 24 ≠ 1`. -/
theorem solvable_of_mod_24_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 24 ≠ 1) : Solvable n := by
  by_cases h13 : n % 24 = 13
  · exact solvable_of_thirteen_mod_24 h13
  · exact solvable_of_mod_twelve_ne_one hn (by omega)

/-- If some divisor `d ≥ 2` of `n` satisfies `d % 24 ≠ 1`, then `4/n` is a sum of three
unit fractions. -/
theorem solvable_of_dvd_mod_24_ne_one {d n : ℕ} (hn : 0 < n) (hd : 2 ≤ d) (hdvd : d ∣ n)
    (h : d % 24 ≠ 1) : Solvable n :=
  Solvable.of_dvd hn hdvd (solvable_of_mod_24_ne_one hd h)

/-- A purely arithmetic certificate for solvability: positive `x, y, z` with
`4xyz = n(yz + xz + xy)`. -/
lemma solvable_of_witness {n x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) : Solvable n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp at h; omega
    · exact h0
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  have hnq : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hxq : (x:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hq : 4 * ((x:ℚ) * y * z) = n * (y * z + x * z + x * y) := by exact_mod_cast h
  field_simp
  linarith [hq]

section SmallPrimes

/-! ### Explicit solutions for the primes `p ≡ 1 [MOD 24]` below `1000` -/

lemma solvable_73 : Solvable 73 :=
  solvable_of_witness (x := 20) (y := 210) (z := 30660)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_97 : Solvable 97 :=
  solvable_of_witness (x := 25) (y := 810) (z := 392850)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_193 : Solvable 193 :=
  solvable_of_witness (x := 50) (y := 1380) (z := 1331700)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_241 : Solvable 241 :=
  solvable_of_witness (x := 62) (y := 2139) (z := 1030998)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_313 : Solvable 313 :=
  solvable_of_witness (x := 80) (y := 3580) (z := 4482160)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_337 : Solvable 337 :=
  solvable_of_witness (x := 85) (y := 9550) (z := 54711950)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_409 : Solvable 409 :=
  solvable_of_witness (x := 104) (y := 6084) (z := 4976712)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_433 : Solvable 433 :=
  solvable_of_witness (x := 110) (y := 6805) (z := 64824430)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_457 : Solvable 457 :=
  solvable_of_witness (x := 115) (y := 17520) (z := 184152720)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_577 : Solvable 577 :=
  solvable_of_witness (x := 145) (y := 27890) (z := 466683370)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_601 : Solvable 601 :=
  solvable_of_witness (x := 152) (y := 13053) (z := 62758824)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_673 : Solvable 673 :=
  solvable_of_witness (x := 170) (y := 16345) (z := 374006290)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_769 : Solvable 769 :=
  solvable_of_witness (x := 194) (y := 21340) (z := 16410460)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma solvable_937 : Solvable 937 :=
  solvable_of_witness (x := 235) (y := 73400) (z := 3232462600)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Every prime `p < 1000` with `p ≡ 1 [MOD 24]` is solvable. -/
theorem solvable_of_prime_one_mod_24_lt_1000 {p : ℕ} (hp : p.Prime) (h1 : p % 24 = 1)
    (h2 : p < 1000) : Solvable p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = 24 * j + 1 := ⟨p / 24, by omega⟩
  have hj : j < 42 := by omega
  interval_cases j <;>
    first
      | (exfalso; revert hp; norm_num; done)
      | exact solvable_73
      | exact solvable_97
      | exact solvable_193
      | exact solvable_241
      | exact solvable_313
      | exact solvable_337
      | exact solvable_409
      | exact solvable_433
      | exact solvable_457
      | exact solvable_577
      | exact solvable_601
      | exact solvable_673
      | exact solvable_769
      | exact solvable_937

/-- **Unconditional partial result.** The Erdős–Straus conjecture holds for all
`2 ≤ n < 1000`. -/
theorem solvable_of_lt_1000 {n : ℕ} (hn : 2 ≤ n) (h : n < 1000) : Solvable n := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hple : p ≤ n := Nat.le_of_dvd (by omega) hpd
  by_cases hm : p % 24 = 1
  · exact Solvable.of_dvd (by omega) hpd
      (solvable_of_prime_one_mod_24_lt_1000 hp hm (by omega))
  · exact Solvable.of_dvd (by omega) hpd (solvable_of_mod_24_ne_one hp.two_le hm)

end SmallPrimes

/-- **Conditional reduction.** The Erdős–Straus conjecture follows from its special case
for primes `p ≡ 1 [MOD 24]`. -/
theorem erdosStraus_of_primes_one_mod_24
    (H : ∀ p : ℕ, p.Prime → p % 24 = 1 → Solvable p) : ErdosStrausConjecture := by
  intro n hn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hsp : Solvable p := by
    by_cases h : p % 24 = 1
    · exact H p hp h
    · exact solvable_of_mod_24_ne_one hp.two_le h
  exact Solvable.of_dvd (by omega) hpd hsp

end Brockian.ErdosStraus

