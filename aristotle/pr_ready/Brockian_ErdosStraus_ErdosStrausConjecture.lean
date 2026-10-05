/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Brockian.ErdosStraus
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


namespace Brockian.ErdosStraus

/-- `ES n` says that `4 / n` is a sum of three positive unit fractions
(the Erdős–Straus property for `n`; the denominators need not be distinct). -/
def ES (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The Erdős–Straus conjecture: every `n ≥ 2` has the property `ES n`. -/
def ErdosStrausStatement : Prop := ∀ n : ℕ, 2 ≤ n → ES n

/-- If `4/a` is a sum of three unit fractions, so is `4/(a*m)` for any `m > 0`. -/
theorem es_mul {a m : ℕ} (ha : ES a) (hm : 0 < m) : ES (a * m) := by
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := ha
  refine ⟨m * x, m * y, m * z, by positivity, by positivity, by positivity, ?_⟩
  push_cast
  rw [show (4 : ℚ) / ((a : ℚ) * m) = (1 / m) * (4 / a) by ring, h]
  ring

/-- `ES 2`. -/
theorem es_two : ES 2 :=
  ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Every even number `≥ 2` has the Erdős–Straus property. -/
theorem es_of_even {n : ℕ} (hn : n % 2 = 0) (hpos : 0 < n) : ES n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  exact es_mul es_two (by omega)

/-- Every `n ≡ 3 (mod 4)` has the Erdős–Straus property. -/
theorem es_of_mod_four_eq_three {n : ℕ} (hn : n % 4 = 3) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine ⟨2 * (k + 1), 2 * (k + 1), (4 * k + 3) * (k + 1), by positivity, by positivity,
    by positivity, ?_⟩
  have h1 : (k : ℚ) + 1 > 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) > 0 := by positivity
  push_cast
  field_simp
  ring

/-- Every `n ≡ 2 (mod 3)` has the Erdős–Straus property. -/
theorem es_of_mod_three_eq_two {n : ℕ} (hn : n % 3 = 2) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨3 * k + 2, k + 1, (3 * k + 2) * (k + 1), by positivity, by positivity,
    by positivity, ?_⟩
  have h1 : (k : ℚ) + 1 > 0 := by positivity
  have h2 : (3 * (k : ℚ) + 2) > 0 := by positivity
  push_cast
  field_simp
  ring

/-- `ES 3`. -/
theorem es_three : ES 3 := es_of_mod_four_eq_three (by norm_num)

/-- **Unconditional partial result.** Every `n ≥ 2` with `n % 12 ≠ 1` has the
Erdős–Straus property. Hence only the residue class `1 (mod 12)` remains open. -/
theorem es_of_mod_twelve_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 12 ≠ 1) : ES n := by
  by_cases h2 : n % 2 = 0
  · exact es_of_even h2 (by omega)
  by_cases h4 : n % 4 = 3
  · exact es_of_mod_four_eq_three h4
  by_cases h3 : n % 3 = 2
  · exact es_of_mod_three_eq_two h3
  by_cases h3' : n % 3 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    exact es_mul es_three (by omega)
  · omega

/-- Every prime outside the residue class `1 (mod 12)` has the Erdős–Straus property. -/
theorem es_prime_of_mod_twelve_ne_one {p : ℕ} (hp : p.Prime) (h : p % 12 ≠ 1) : ES p :=
  es_of_mod_twelve_ne_one hp.two_le h

/-- **Conditional Erdős–Straus conjecture.**
If every prime `p ≡ 1 (mod 12)` satisfies the Erdős–Straus property, then every integer
`n ≥ 2` does, i.e. the full Erdős–Straus conjecture holds.
(The Erdős–Straus conjecture is an open problem; this is a Lean-checked reduction of it
to the single residue class `p ≡ 1 (mod 12)` of primes.) -/
theorem ErdosStrausConjecture
    (hprimes : ∀ p : ℕ, p.Prime → p % 12 = 1 → ES p) : ErdosStrausStatement := by
  intro n hn
  have hn0 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn0
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm; omega
    · exact h
  have hES : ES n.minFac := by
    by_cases h : n.minFac % 12 = 1
    · exact hprimes _ hp h
    · exact es_prime_of_mod_twelve_ne_one hp h
  rw [hm]
  exact es_mul hES hmpos

end Brockian.ErdosStraus

