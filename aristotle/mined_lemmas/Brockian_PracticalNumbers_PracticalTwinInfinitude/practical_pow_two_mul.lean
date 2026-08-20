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

open Finset

namespace Brockian.PracticalNumbers

/-!
## Overview

A positive integer `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n`.
We prove that there are infinitely many `n` with `n` and `n + 2` both practical.

The construction: fix a large `a`, let `3 ^ b` be the largest power of `3` with `3 ^ b ≤ 2 ^ (a+1)`,
and let `s` be the representative in `[1, 3 ^ b)` of `-(2 ^ (a-1))⁻¹ mod 3 ^ b`.  Then

* `n = 2 ^ a * s` is practical because `s ≤ 3 ^ b ≤ 2 ^ (a+1) = σ(2 ^ a) + 1`;
* `n + 2 = 2 * (2 ^ (a-1) * s + 1)` where `3 ^ b` divides `2 ^ (a-1) * s + 1`, so writing
  `2 ^ (a-1) * s + 1 = 3 ^ b' * v` with `3 ∤ v` and `b' ≥ b`, we get `v ≤ 2 ^ (a-1) < 3 ^ (b'+1)`,
  which makes `2 * 3 ^ b' * v` practical.

Practicality of these two families is obtained from an explicit complete set of divisors
(`P2` for powers of two, `D3` for `2 * 3 ^ b`) together with a combination lemma
(`subsetSum_combine`), a constructive version of Stewart's criterion.
-/

/-- `SubsetSum D t` means `t` is the sum of a subset of the finite set `D`. -/

lemma practical_pow_two_mul : ∀ s : ℕ, 0 < s → ∀ a : ℕ, s ≤ 2 ^ (a + 1) →
    Practical (2 ^ a * s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs a hle
    rcases Nat.even_or_odd s with he | ho
    · obtain ⟨s', rfl⟩ := he
      have h1 : 0 < s' := by omega
      have h2 : s' ≤ 2 ^ (a + 1 + 1) := by
        have : (2 : ℕ) ^ (a + 1) ≤ 2 ^ (a + 1 + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hres := ih s' (by omega) h1 (a + 1) h2
      have heq : 2 ^ (a + 1) * s' = 2 ^ a * (s' + s') := by rw [pow_succ]; ring
      rwa [heq] at hres
    · have hsum := sum_P2 a
      have hcomp : ∀ t ≤ ∑ d ∈ P2 a, d, SubsetSum (P2 a) t := by
        intro t ht
        rw [hsum] at ht
        exact subsetSum_P2 a ht
      have hodd2 : ¬ 2 ∣ s := by
        obtain ⟨k, hk⟩ := ho
        omega
      by_cases h1 : 1 < s
      case neg =>
        have hs1 : s = 1 := by omega
        subst hs1
        rw [Nat.mul_one]
        exact practical_of_completeSet ((by positivity)) (P2 a)
          (fun d hd => P2_dvd hd) (pow_mem_P2 a) hcomp
      case pos =>
        have hcoll : ∀ d ∈ P2 a, ∀ d' ∈ P2 a, s * d ≠ d' := by
          intro d _ d' hd' heq
          have hdvd : s ∣ 2 ^ a := dvd_trans ⟨d, heq.symm⟩ (P2_dvd hd')
          obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp at h1
          · exact hodd2 (dvd_pow_self 2 (by omega))
        have hres := practical_of_combine ((by positivity)) (P2 a)
          (fun d hd => P2_dvd hd) (pow_mem_P2 a) hcomp (by omega) (by omega) hcoll
        rwa [Nat.mul_comm] at hres

/-- If `v` is coprime to `6` and `v ≤ 3^(b+1)` then `2 * 3^b * v` is practical. -/
