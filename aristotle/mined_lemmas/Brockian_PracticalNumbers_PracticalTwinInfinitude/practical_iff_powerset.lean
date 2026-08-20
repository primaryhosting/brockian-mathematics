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

lemma practical_iff_powerset (n : ℕ) :
    Practical n ↔
      0 < n ∧ ∀ m ∈ Finset.range (n + 1), ∃ S ∈ n.divisors.powerset, ∑ d ∈ S, d = m := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun m hm => ?_⟩
    obtain ⟨S, hS, hsum⟩ := h m (by rw [Finset.mem_range] at hm; omega)
    exact ⟨S, Finset.mem_powerset.mpr hS, hsum⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun m hm => ?_⟩
    obtain ⟨S, hS, hsum⟩ := h m (Finset.mem_range.mpr (by omega))
    exact ⟨S, Finset.mem_powerset.mp hS, hsum⟩

example : Practical 6 := by rw [practical_iff_powerset]; decide
example : Practical 8 := by rw [practical_iff_powerset]; decide
example : Practical 16 := by rw [practical_iff_powerset]; decide
example : Practical 18 := by rw [practical_iff_powerset]; decide
example : ¬ Practical 5 := by rw [practical_iff_powerset]; decide
example : ¬ Practical 10 := by rw [practical_iff_powerset]; decide

-- the twin pair produced by the construction for `a = 4`
example : Practical 160 := practical_pow_two_mul 10 (by norm_num) 4 (by norm_num)
example : Practical 162 := by
  have := practical_two_pow_three_mul (b := 4) (v := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this
  exact this

/-- Main theorem: there are infinitely many `n` such that both `n` and `n + 2` are practical. -/
