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
The Erdős–Straus conjecture asserts that for every integer `n ≥ 2` the fraction
`4/n` can be written as a sum of three positive unit fractions.  The conjecture
is open, so what is proved here is a *conditional reduction*: the full statement
follows from the special case of primes `p ≡ 1 (mod 24)`.

Unconditionally we prove solvability for every `n ≥ 2` that has a divisor `≥ 2`
which is not congruent to `1` modulo `24`; in particular for every `n ≥ 2` with
`n % 24 ≠ 1`.
-/

namespace Brockian.ErdosStraus

/-- `4/n` is a sum of three positive unit fractions. -/
def ErdosStrausSolvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- Certificate form: an integral identity witnessing `4/n = 1/x + 1/y + 1/z`. -/
theorem solvable_of_eq (n x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) : ErdosStrausSolvable n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h' : (4 : ℚ) * (x * y * z) = n * (y * z + x * z + x * y) := by exact_mod_cast h
  field_simp
  linarith [h']

/-- Solvability passes from a divisor to its multiples. -/
theorem solvable_of_dvd {m n : ℕ} (hn : 0 < n) (hmn : m ∣ n)
    (h : ErdosStrausSolvable m) : ErdosStrausSolvable n := by
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ := h
  obtain ⟨k, rfl⟩ := hmn
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0] at hn
    · exact h0
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0] at hn
    · exact h0
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  refine ⟨x * k, y * k, z * k, by positivity, by positivity, by positivity, ?_⟩
  have key : (4 : ℚ) / ((m : ℚ) * k) = ((1 / x + 1 / y + 1 / z)) / k := by
    rw [← heq, div_div]
  push_cast
  rw [key]
  field_simp

/-- Even `n`: `4/(2m) = 1/m + 1/(2m) + 1/(2m)`. -/
theorem solvable_of_even {n : ℕ} (hn : 0 < n) (h : n % 2 = 0) : ErdosStrausSolvable n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : 0 < m := by omega
  exact solvable_of_eq _ m (2 * m) (2 * m) hm (by omega) (by omega) (by ring)

/-- `n ≡ 2 (mod 3)`, say `n = 3k+2`: `4/n = 1/(k+1) + 1/n + 1/(n(k+1))`. -/
theorem solvable_of_mod_three_eq_two {n : ℕ} (h : n % 3 = 2) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine solvable_of_eq _ (k + 1) (3 * k + 2) ((3 * k + 2) * (k + 1)) (by omega) (by omega)
    (by positivity) (by ring)

/-- `n ≡ 3 (mod 4)`, say `n = 4k+3`:
`4/n = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1))`. -/
theorem solvable_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine solvable_of_eq _ (k + 1) (2 * (4 * k + 3) * (k + 1)) (2 * (4 * k + 3) * (k + 1))
    (by omega) (by positivity) (by positivity) (by ring)

/-- `n ≡ 5 (mod 8)`, say `n = 8k+5`:
`4/n = 1/(2(k+1)) + 1/(n(k+1)) + 1/(2n(k+1))`. -/
theorem solvable_of_mod_eight_eq_five {n : ℕ} (h : n % 8 = 5) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
  refine solvable_of_eq _ (2 * (k + 1)) ((8 * k + 5) * (k + 1)) (2 * (8 * k + 5) * (k + 1))
    (by omega) (by positivity) (by positivity) (by ring)

/-- `4/3 = 1/1 + 1/6 + 1/6`. -/
theorem solvable_three : ErdosStrausSolvable 3 :=
  solvable_of_eq 3 1 6 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Unconditional result: `4/n` is a sum of three unit fractions whenever
`n ≥ 2` is not congruent to `1` modulo `24`. -/
theorem solvable_of_mod_24_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 24 ≠ 1) :
    ErdosStrausSolvable n := by
  by_cases h2 : n % 2 = 0
  · exact solvable_of_even (by omega) h2
  by_cases h3 : n % 3 = 0
  · exact solvable_of_dvd (by omega) (by omega) solvable_three
  by_cases h3' : n % 3 = 2
  · exact solvable_of_mod_three_eq_two h3'
  by_cases h4 : n % 4 = 3
  · exact solvable_of_mod_four_eq_three h4
  by_cases h8 : n % 8 = 5
  · exact solvable_of_mod_eight_eq_five h8
  · exact absurd (by omega : n % 24 = 1) h

/-- Solvability for any `n ≥ 2` having a divisor `≥ 2` that is not `1` mod `24`. -/
theorem solvable_of_exists_divisor {n : ℕ} (hn : 0 < n)
    (hd : ∃ d, d ∣ n ∧ 2 ≤ d ∧ d % 24 ≠ 1) : ErdosStrausSolvable n := by
  obtain ⟨d, hdvd, hd2, hd24⟩ := hd
  exact solvable_of_dvd hn hdvd (solvable_of_mod_24_ne_one hd2 hd24)

/-- **Conditional Erdős–Straus conjecture.**  The Erdős–Straus conjecture (for
every `n ≥ 2` the fraction `4/n` is a sum of three positive unit fractions)
follows from its special case for primes congruent to `1` modulo `24`. -/
theorem ErdosStrausConjecture
    (h : ∀ p : ℕ, p.Prime → p % 24 = 1 → ErdosStrausSolvable p) :
    ∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n := by
  intro n hn
  have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  by_cases hp24 : n.minFac % 24 = 1
  · exact solvable_of_dvd (by omega) (Nat.minFac_dvd n) (h _ hp hp24)
  · exact solvable_of_dvd (by omega) (Nat.minFac_dvd n)
      (solvable_of_mod_24_ne_one hp.two_le hp24)

/-- The Erdős–Straus conjecture is *equivalent* to its special case for primes
congruent to `1` modulo `24`. -/
theorem erdosStraus_iff_primes_one_mod_24 :
    (∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n) ↔
      (∀ p : ℕ, p.Prime → p % 24 = 1 → ErdosStrausSolvable p) := by
  refine ⟨fun h p hp _ => h p hp.two_le, ErdosStrausConjecture⟩

end Brockian.ErdosStraus

