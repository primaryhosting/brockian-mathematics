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

lemma subsetSum_P2 (A : ℕ) {t : ℕ} (h : t ≤ 2 ^ (A + 1) - 1) : SubsetSum (P2 A) t := by
  induction A generalizing t with
  | zero =>
    have ht : t ≤ 1 := by norm_num at h; omega
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp [P2], by simp⟩
  | succ A ih =>
    by_cases hc : t ≤ 2 ^ (A + 1) - 1
    · exact (ih hc).mono (by rw [P2]; exact Finset.subset_insert _ _)
    · push_neg at hc
      have h2 : (2 : ℕ) ^ (A + 1 + 1) = 2 ^ (A + 1) + 2 ^ (A + 1) := by rw [pow_succ]; ring
      have h1 : (1 : ℕ) ≤ 2 ^ (A + 1) := Nat.one_le_two_pow
      have hle : t - 2 ^ (A + 1) ≤ 2 ^ (A + 1) - 1 := by omega
      have hres := (ih hle).insert_of (pow_notMem_P2 A)
      have heq : t - 2 ^ (A + 1) + 2 ^ (A + 1) = t := by omega
      rw [heq] at hres
      rw [P2]
      exact hres

/-! ## The sets `{1, 2, 3, 6, …, 3^b, 2·3^b}` -/

/-- `D3 b = {2^e * 3^j : e ≤ 1, j ≤ b}`. -/
