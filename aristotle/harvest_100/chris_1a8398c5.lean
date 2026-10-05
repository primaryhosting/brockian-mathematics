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

namespace Brockian.ErdosStraus

/-- `ErdosStrausSolvable n` says that `4 / n` is a sum of three unit fractions with
positive natural denominators. -/
def ErdosStrausSolvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (1 : ℚ) / x + 1 / y + 1 / z = 4 / n

/-- The Erdős–Straus conjecture: for every `n ≥ 2` the fraction `4 / n` can be written as a
sum of three unit fractions. -/
def ErdosStrausConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n

/-- Master criterion: a purely arithmetic (natural number) identity certifying solvability. -/
theorem solvable_of_nat_eq {n x y z : ℕ} (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : n * (y * z) + n * (x * z) + n * (x * y) = 4 * (x * y * z)) :
    ErdosStrausSolvable n := by
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h' : (n : ℚ) * (y * z) + n * (x * z) + n * (x * y) = 4 * (x * y * z) := by
    exact_mod_cast h
  field_simp
  linarith [h']

/-- Solvability passes from a divisor to its multiples. -/
theorem solvable_of_dvd {d n : ℕ} (hn : 0 < n) (hdvd : d ∣ n)
    (hs : ErdosStrausSolvable d) : ErdosStrausSolvable n := by
  obtain ⟨c, rfl⟩ := hdvd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := hs
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h] at hn
    · exact h
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · simp [h] at hn
    · exact h
  refine ⟨x * c, y * c, z * c, by positivity, by positivity, by positivity, ?_⟩
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  push_cast
  have key : (1 : ℚ) / (x * c) + 1 / (y * c) + 1 / (z * c)
      = (1 / c) * ((1 : ℚ) / x + 1 / y + 1 / z) := by
    field_simp
  rw [key, hxyz]
  field_simp

/-! ### Solvable residue classes -/

/-- `4 / n` is a sum of three unit fractions whenever `n` is even. -/
theorem solvable_of_even {n : ℕ} (hn : 0 < n) (h : n % 2 = 0) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  have hk : 0 < k := by omega
  exact solvable_of_nat_eq hn hk (show 0 < 2 * k by omega) (show 0 < 2 * k by omega) (by ring)

/-- `4 / n` is a sum of three unit fractions whenever `3 ∣ n`. -/
theorem solvable_of_three_dvd {n : ℕ} (hn : 0 < n) (h : n % 3 = 0) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
  have hk : 0 < k := by omega
  exact solvable_of_nat_eq hn hk (show 0 < 6 * k by omega) (show 0 < 6 * k by omega) (by ring)

/-- `4 / n` is a sum of three unit fractions whenever `n ≡ 3 [MOD 4]`. -/
theorem solvable_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  exact solvable_of_nat_eq (by omega) (show 0 < k + 1 by omega)
    (show 0 < 2 * ((4 * k + 3) * (k + 1)) by positivity)
    (show 0 < 2 * ((4 * k + 3) * (k + 1)) by positivity) (by ring)

/-- `4 / n` is a sum of three unit fractions whenever `n ≡ 2 [MOD 3]`. -/
theorem solvable_of_mod_three_eq_two {n : ℕ} (h : n % 3 = 2) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  exact solvable_of_nat_eq (by omega) (show 0 < k + 1 by omega)
    (show 0 < 3 * k + 2 by omega)
    (show 0 < (3 * k + 2) * (k + 1) by positivity) (by ring)

/-- `4 / n` is a sum of three unit fractions whenever `n ≡ 5 [MOD 8]`. -/
theorem solvable_of_mod_eight_eq_five {n : ℕ} (h : n % 8 = 5) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
  exact solvable_of_nat_eq (by omega) (show 0 < 2 * k + 2 by omega)
    (show 0 < (8 * k + 5) * (2 * k + 2) by positivity)
    (show 0 < (8 * k + 5) * (k + 1) by positivity) (by ring)

/-- **Main unconditional result.** The Erdős–Straus conjecture holds for every `n ≥ 2` whose
residue modulo `24` is different from `1`. -/
theorem solvable_of_mod_24_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 24 ≠ 1) :
    ErdosStrausSolvable n := by
  have hn0 : 0 < n := by omega
  have key : n % 2 = 0 ∨ n % 3 = 0 ∨ n % 4 = 3 ∨ n % 3 = 2 ∨ n % 8 = 5 := by omega
  rcases key with h' | h' | h' | h' | h'
  · exact solvable_of_even hn0 h'
  · exact solvable_of_three_dvd hn0 h'
  · exact solvable_of_mod_four_eq_three h'
  · exact solvable_of_mod_three_eq_two h'
  · exact solvable_of_mod_eight_eq_five h'

/-- **Reduction to primes.** The full Erdős–Straus conjecture is equivalent to its restriction
to primes congruent to `1` modulo `24`. -/
theorem erdosStrausConjecture_iff_primes :
    ErdosStrausConjecture ↔ ∀ p : ℕ, p.Prime → p % 24 = 1 → ErdosStrausSolvable p := by
  constructor
  · intro hc p hp _
    exact hc p hp.two_le
  · intro h n hn
    have hn0 : 0 < n := by omega
    have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    refine solvable_of_dvd hn0 hdvd ?_
    by_cases hm : n.minFac % 24 = 1
    · exact h _ hp hm
    · exact solvable_of_mod_24_ne_one hp.two_le hm

end Brockian.ErdosStraus

