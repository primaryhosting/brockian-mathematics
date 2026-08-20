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

lemma subsetSum_D3 (b : ℕ) {t : ℕ} (h : t ≤ ∑ d ∈ D3 b, d) : SubsetSum (D3 b) t := by
  induction b generalizing t with
  | zero =>
    have hsum : ∑ d ∈ D3 0, d = 3 := by norm_num [D3]
    rw [hsum] at h
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by norm_num [D3], by simp⟩
    · exact ⟨{2}, by norm_num [D3], by simp⟩
    · exact ⟨{1, 2}, by norm_num [D3], by norm_num⟩
  | succ b ih =>
    set p := (3 : ℕ) ^ (b + 1) with hp
    set Sm := ∑ d ∈ D3 b, d with hSm
    have hpS : p ≤ Sm := pow_le_sum_D3 b
    have hsum : ∑ d ∈ D3 (b + 1), d = Sm + 3 * p := sum_D3_succ b
    have h3pos : 0 < (3 : ℕ) ^ b := by positivity
    have hp3 : p = 3 * 3 ^ b := by rw [hp]; ring
    have hnot1 : 2 * p ∉ D3 b := by
      intro hmem
      have h1 := D3_le hmem
      omega
    have hnot2 : p ∉ insert (2 * p) (D3 b) := by
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with h1 | h1
      · omega
      · have := D3_le h1
        omega
    rw [hsum] at h
    have hstep : ∀ r ≤ Sm, SubsetSum (insert (2 * p) (D3 b)) r := fun r hr =>
      (ih hr).mono (Finset.subset_insert _ _)
    rw [D3]
    by_cases hc : t ≤ Sm
    · exact (hstep t hc).mono (Finset.subset_insert _ _)
    push_neg at hc
    by_cases hc2 : t ≤ Sm + p
    · -- use p
      have hres := (hstep (t - p) (by omega)).insert_of hnot2
      have heq : t - p + p = t := by omega
      rwa [heq] at hres
    push_neg at hc2
    by_cases hc3 : t ≤ Sm + 2 * p
    · -- use 2p
      have hres := ((ih (show t - 2 * p ≤ Sm by omega)).insert_of hnot1)
      have heq : t - 2 * p + 2 * p = t := by omega
      rw [heq] at hres
      exact hres.mono (Finset.subset_insert _ _)
    · -- use both p and 2p
      push_neg at hc3
      have hres := ((ih (show t - 3 * p ≤ Sm by omega)).insert_of hnot1).insert_of hnot2
      have heq : t - 3 * p + 2 * p + p = t := by omega
      rwa [heq] at hres

/-! ## Two families of practical numbers -/

/-- If `0 < s ≤ 2^(a+1)` then `2^a * s` is practical. -/
