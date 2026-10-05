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

/-- `Solvable n` says that `4 / n` can be written as a sum of three unit fractions
with positive natural denominators. -/
def Solvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- **Erdős–Straus conjecture**: for every `n ≥ 2` the fraction `4/n` is a sum of three
unit fractions. -/
def ErdosStrausConjecture : Prop := ∀ n : ℕ, 2 ≤ n → Solvable n

/-- Scaling: a solution for `n` yields a solution for any multiple `k * n` (`k ≥ 1`). -/
theorem solvable_mul (k n : ℕ) (hk : 0 < k) (h : Solvable n) : Solvable (k * n) := by
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := h
  refine ⟨k * x, k * y, k * z, Nat.mul_pos hk hx, Nat.mul_pos hk hy, Nat.mul_pos hk hz, ?_⟩
  have e0 : (4 : ℚ) / ((k * n : ℕ) : ℚ) = (4 / (n : ℚ)) / (k : ℚ) := by
    push_cast; rw [div_div, mul_comm]
  have e1 : ∀ w : ℕ, (1 : ℚ) / ((k * w : ℕ) : ℚ) = (1 / (w : ℚ)) / (k : ℚ) := by
    intro w; push_cast; rw [div_div, mul_comm]
  rw [e0, e1, e1, e1, div_add_div_same, div_add_div_same, h]

/-- Divisibility form of the scaling lemma. -/
theorem solvable_of_dvd {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) (h : Solvable d) : Solvable n := by
  obtain ⟨c, rfl⟩ := hd
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at hn
    · exact hc
  rw [mul_comm]
  exact solvable_mul c d hc h

theorem solvable_two : Solvable 2 :=
  ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem solvable_three : Solvable 3 :=
  ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The identity `4/(4k+3) = 1/(k+1) + 1/(2(4k+3)(k+1)) + 1/(2(4k+3)(k+1))`. -/
theorem solvable_four_mul_add_three (k : ℕ) : Solvable (4 * k + 3) := by
  refine ⟨k + 1, 2 * (4 * k + 3) * (k + 1), 2 * (4 * k + 3) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The identity `4/(3k+2) = 1/(3k+2) + 1/(k+1) + 1/((3k+2)(k+1))`. -/
theorem solvable_three_mul_add_two (k : ℕ) : Solvable (3 * k + 2) := by
  refine ⟨3 * k + 2, k + 1, (3 * k + 2) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Unconditional partial result: `4/n` is a sum of three unit fractions for every `n ≥ 2`
which is not congruent to `1` modulo `12`. -/
theorem solvable_of_mod_twelve_ne_one (n : ℕ) (hn : 2 ≤ n) (h : n % 12 ≠ 1) : Solvable n := by
  have hn0 : 0 < n := by omega
  rcases Nat.even_or_odd n with he | ho
  · exact solvable_of_dvd hn0 he.two_dvd solvable_two
  · by_cases h3 : 3 ∣ n
    · exact solvable_of_dvd hn0 h3 solvable_three
    · have h3'' : ¬ n % 3 = 0 := fun hc => h3 (Nat.dvd_of_mod_eq_zero hc)
      have h2' : n % 2 = 1 := Nat.odd_iff.mp ho
      rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with h3' | h3'
      · -- `n % 3 = 1` together with `n` odd and `n % 12 ≠ 1` forces `n % 4 = 3`
        have hk : n = 4 * (n / 4) + 3 := by omega
        rw [hk]
        exact solvable_four_mul_add_three _
      · have hk : n = 3 * (n / 3) + 2 := by omega
        rw [hk]
        exact solvable_three_mul_add_two _

/-- Conditional reduction: the Erdős–Straus conjecture follows from its special case for
primes `p ≡ 1 (mod 12)`. -/
theorem erdosStrausConjecture_of_primes
    (H : ∀ p : ℕ, p.Prime → p % 12 = 1 → Solvable p) : ErdosStrausConjecture := by
  intro n hn
  have hn0 : 0 < n := by omega
  have hn1 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  by_cases h : n.minFac % 12 = 1
  · exact solvable_of_dvd hn0 hdvd (H _ hp h)
  · exact solvable_of_dvd hn0 hdvd (solvable_of_mod_twelve_ne_one _ hp.two_le h)

end Brockian.ErdosStraus

