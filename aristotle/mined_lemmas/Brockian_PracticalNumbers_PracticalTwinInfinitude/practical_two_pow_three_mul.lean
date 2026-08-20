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

lemma practical_two_pow_three_mul {b v : ℕ} (hv : 0 < v) (h2 : ¬ 2 ∣ v) (h3 : ¬ 3 ∣ v)
    (hle : v ≤ 3 ^ (b + 1)) : Practical (2 * 3 ^ b * v) := by
  have hm0 : 0 < 2 * 3 ^ b := by positivity
  have hcomp : ∀ t ≤ ∑ d ∈ D3 b, d, SubsetSum (D3 b) t := fun t ht => subsetSum_D3 b ht
  have hsum : 3 ^ (b + 1) ≤ ∑ d ∈ D3 b, d := pow_le_sum_D3 b
  by_cases h1 : 1 < v
  case neg =>
    have hv1 : v = 1 := by omega
    subst hv1
    rw [Nat.mul_one]
    exact practical_of_completeSet hm0 (D3 b) (fun d hd => D3_dvd hd) (two_mul_pow_mem_D3 b) hcomp
  case pos =>
    have hcoll : ∀ d ∈ D3 b, ∀ d' ∈ D3 b, v * d ≠ d' := by
      intro d _ d' hd' heq
      have hdvd : v ∣ 2 * 3 ^ b := dvd_trans ⟨d, heq.symm⟩ (D3_dvd hd')
      have hc2 : Nat.Coprime v 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
      have hc3 : Nat.Coprime v (3 ^ b) :=
        (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm).pow_right b
      have : v = 1 := (hc2.mul_right hc3).eq_one_of_dvd hdvd
      omega
    have hres := practical_of_combine hm0 (D3 b) (fun d hd => D3_dvd hd) (two_mul_pow_mem_D3 b)
      hcomp (by omega) (by omega) hcoll
    rwa [Nat.mul_comm] at hres

/-! ## The construction -/

/-- For every `N` there is a practical `n > N` with `n + 2` practical. -/
