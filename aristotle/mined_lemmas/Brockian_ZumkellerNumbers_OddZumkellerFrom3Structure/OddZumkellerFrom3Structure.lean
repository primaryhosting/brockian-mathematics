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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

theorem OddZumkellerFrom3Structure (a m : ℕ) (ha : 3 ≤ a) (hodd : Odd m)
    (hcop : Nat.Coprime 105 m) :
    Odd (3 ^ a * 35 * m) ∧ IsZumkeller (3 ^ a * 35 * m) ∧
      3 ^ a ∣ 3 ^ a * 35 * m ∧ ¬ (3 ^ (a + 1) ∣ 3 ^ a * 35 * m) := by
  have hm0 : 0 < m := by
    have := Nat.odd_iff.mp hodd
    omega
  have hc3 : Nat.Coprime 3 m := Nat.Coprime.coprime_dvd_left (by norm_num) hcop
  have hc35 : Nat.Coprime 35 m := Nat.Coprime.coprime_dvd_left (by norm_num) hcop
  have hcm : Nat.Coprime (3 ^ a * 35) m :=
    Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hc3) hc35
  refine ⟨?_, zumkeller_mul_of_coprime (zumkeller_three_pow_mul_35 ha) hm0 hcm,
    ⟨35 * m, by ring⟩, ?_⟩
  · exact (Odd.mul (Odd.pow (by decide)) (by decide)).mul hodd
  · intro hdvd
    have h1 : (3 : ℕ) ^ a * 3 ∣ 3 ^ a * (35 * m) := by
      rw [← mul_assoc]
      rw [pow_succ] at hdvd
      exact hdvd
    have h2 : (3 : ℕ) ∣ 35 * m := (mul_dvd_mul_iff_left (by positivity : (3 : ℕ) ^ a ≠ 0)).mp h1
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h2 with h | h
    · norm_num at h
    · have h3 : (3 : ℕ) ∣ Nat.gcd 3 m := Nat.dvd_gcd dvd_rfl h
      rw [hc3] at h3
      norm_num at h3

/-- There are infinitely many odd Zumkeller numbers. -/
