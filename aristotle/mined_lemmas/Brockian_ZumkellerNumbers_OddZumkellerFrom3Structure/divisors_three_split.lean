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

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is a *Zumkeller number* if its set of divisors can be split into two
parts of equal sum, i.e. there is a set `S` of divisors of `n` whose sum is half of `σ(n)`. -/

lemma divisors_three_split (a : ℕ) :
    ((3:ℕ) ^ (a + 4) * 35).divisors
      = (945 : ℕ).divisors ∪ (((3:ℕ) ^ a * 35).divisors.image (fun d => 81 * d)) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hx, -⟩
    rw [Nat.dvd_mul] at hx
    obtain ⟨y, z, hy, hz, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hy
    rcases le_or_gt i 3 with h | h
    · left
      refine ⟨?_, by norm_num⟩
      have h1 : (3:ℕ) ^ i * z ∣ 3 ^ 3 * 35 := mul_dvd_mul (pow_dvd_pow 3 h) hz
      simpa using h1
    · right
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩
      refine ⟨3 ^ j * z, ⟨mul_dvd_mul (pow_dvd_pow 3 (by omega)) hz, by positivity⟩, by ring⟩
  · rintro (⟨hx, -⟩ | ⟨y, ⟨hy, -⟩, rfl⟩)
    · refine ⟨hx.trans ?_, by positivity⟩
      have h945 : (945 : ℕ) = 3 ^ 3 * 35 := by norm_num
      rw [h945]
      exact mul_dvd_mul (pow_dvd_pow 3 (by omega)) dvd_rfl
    · refine ⟨?_, by positivity⟩
      have h81 : (81 : ℕ) * (3 ^ a * 35) = 3 ^ (a + 4) * 35 := by ring
      calc 81 * y ∣ 81 * (3 ^ a * 35) := mul_dvd_mul_left _ hy
        _ = 3 ^ (a + 4) * 35 := h81

