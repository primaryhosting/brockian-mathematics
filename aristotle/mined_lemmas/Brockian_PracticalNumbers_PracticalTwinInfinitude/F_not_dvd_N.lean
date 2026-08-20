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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A natural number `n` is *practical* if it is positive and every `m ≤ n` can be written
as a sum of distinct divisors of `n`. -/

lemma F_not_dvd_N (i : ℕ) : ¬ (F i ∣ N i) := by
  intro hdvd
  have h := N_add_two i
  have h2 := two_le_pow i
  have heven : 2 ∣ 2 ^ (2 ^ i) := dvd_pow_self 2 (Nat.two_pow_pos i).ne'
  have he : N i + 4 = 2 * F i := by simp only [F]; omega
  have hF4 : F i ∣ N i + 4 := ⟨2, by omega⟩
  have h4 : F i ∣ 4 := (Nat.dvd_add_right hdvd).mp hF4
  have hle : F i ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  have hF3 : F i = 3 := by
    simp only [F] at hle ⊢
    omega
  rw [hF3] at h4
  omega

