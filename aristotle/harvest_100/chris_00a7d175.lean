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
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausSolvable n` states that `4 / n` can be written as a sum of three
unit fractions with positive integer denominators. -/
def ErdosStrausSolvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- A two-term representation `4 / n = 1 / x + 1 / w` yields a three-term one, using
the splitting `1 / w = 1 / (w + 1) + 1 / (w * (w + 1))`. -/
lemma solvable_of_two_term (n x w : ℕ) (hx : 0 < x) (hw : 0 < w)
    (h : (4 : ℚ) / n = 1 / x + 1 / w) : ErdosStrausSolvable n := by
  refine ⟨x, w + 1, w * (w + 1), hx, by omega, by positivity, ?_⟩
  have hw' : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hw.ne'
  rw [h]
  push_cast
  field_simp
  ring

/-- For `n ≡ 3 (mod 4)`, writing `n = 4k + 3` we have
`4 / n = 1 / (k + 1) + 1 / (n * (k + 1))`. -/
lemma solvable_three_mod_four (n : ℕ) (h : n % 4 = 3) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine solvable_of_two_term _ (k + 1) ((4 * k + 3) * (k + 1)) (by omega) (by positivity) ?_
  push_cast
  have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-- For `n ≡ 2 (mod 3)`, writing `n = 3k + 2` we have
`4 / n = 1 / n + 1 / (k + 1) + 1 / (n * (k + 1))`. -/
lemma solvable_two_mod_three (n : ℕ) (h : n % 3 = 2) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨3 * k + 2, k + 1, (3 * k + 2) * (k + 1), by omega, by omega, by positivity, ?_⟩
  push_cast
  have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- Solvability propagates from a divisor to its multiples. -/
lemma solvable_of_dvd {m n : ℕ} (hn : 0 < n) (hdvd : m ∣ n)
    (h : ErdosStrausSolvable m) : ErdosStrausSolvable n := by
  obtain ⟨c, rfl⟩ := hdvd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := h
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hxq : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  refine ⟨x * c, y * c, z * c, by positivity, by positivity, by positivity, ?_⟩
  push_cast
  rw [div_mul_eq_div_div, hxyz]
  field_simp

/-- `4 / 2` is a sum of three unit fractions. -/
lemma solvable_two : ErdosStrausSolvable 2 := solvable_two_mod_three 2 rfl

/-- `4 / 3` is a sum of three unit fractions. -/
lemma solvable_three : ErdosStrausSolvable 3 := solvable_three_mod_four 3 rfl

/-- Unconditional part: the Erdős–Straus equation is solvable for every `n ≥ 2`
which is not congruent to `1` modulo `12`. -/
theorem solvable_of_ne_one_mod_twelve (n : ℕ) (hn : 2 ≤ n) (h : n % 12 ≠ 1) :
    ErdosStrausSolvable n := by
  have hn0 : 0 < n := by omega
  rcases Nat.eq_zero_or_pos (n % 2) with h2 | h2
  · exact solvable_of_dvd hn0 (Nat.dvd_of_mod_eq_zero h2) solvable_two
  rcases Nat.eq_zero_or_pos (n % 3) with h3 | h3
  · exact solvable_of_dvd hn0 (Nat.dvd_of_mod_eq_zero h3) solvable_three
  · have hcase : n % 4 = 3 ∨ n % 3 = 2 := by omega
    rcases hcase with h4 | h4
    · exact solvable_three_mod_four n h4
    · exact solvable_two_mod_three n h4

/-- The Erdős–Straus conjecture, reduced to its hard prime case: if `4 / p` is a sum of
three unit fractions for every prime `p ≡ 1 (mod 12)`, then `4 / n` is a sum of three
unit fractions for every `n ≥ 2`.

The reduction itself is proved unconditionally here; the hypothesis isolates exactly the
open part of the conjecture. -/
theorem ErdosStrausConjecture
    (hprime : ∀ p : ℕ, p.Prime → p % 12 = 1 → ErdosStrausSolvable p) :
    ∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n := by
  intro n hn
  have hn0 : 0 < n := by omega
  by_cases h : n % 12 = 1
  · set p := n.minFac with hp
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpd : p ∣ n := Nat.minFac_dvd n
    by_cases h4 : p % 4 = 3
    · exact solvable_of_dvd hn0 hpd (solvable_three_mod_four p h4)
    by_cases h3 : p % 3 = 2
    · exact solvable_of_dvd hn0 hpd (solvable_two_mod_three p h3)
    refine solvable_of_dvd hn0 hpd (hprime p hpp ?_)
    have hp2 : p ≠ 2 := by
      rintro h2
      have hd : (2 : ℕ) ∣ n := h2 ▸ hpd
      omega
    have hp3 : p ≠ 3 := by
      rintro h3'
      have hd : (3 : ℕ) ∣ n := h3' ▸ hpd
      omega
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
    have hpne3 : p % 3 ≠ 0 := by
      intro hd
      exact hp3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp
        (Nat.dvd_of_mod_eq_zero hd)).symm)
    omega
  · exact solvable_of_ne_one_mod_twelve n hn h

end Brockian.ErdosStraus

