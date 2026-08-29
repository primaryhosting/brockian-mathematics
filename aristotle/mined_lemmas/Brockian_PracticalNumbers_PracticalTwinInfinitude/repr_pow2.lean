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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n`.
We prove that there are infinitely many `n` such that `n` and `n + 2` are both practical.

The proof is completely explicit.  Two families of practical numbers are established by
direct subset-sum arguments:

* `2 ^ k * u` is practical whenever `u` is odd and `u ≤ 2 ^ (k+1)`;
* `2 * 3 ^ b * t` is practical whenever `t` is odd, prime to `3`, and `t ≤ 3 ^ b`.

Given `b ≥ 1`, put `s = Nat.log 2 (3 ^ b)`, so `2 ^ s ≤ 3 ^ b < 2 ^ (s+1)`, and let `M` be the
Chinese-remainder solution of `M ≡ 0 [MOD 3 ^ b]`, `M ≡ -1 [MOD 2 ^ s]` with `M < 3 ^ b * 2 ^ s`.
Then `2 * M` lies in the second family and `2 * M + 2 = 2 * (M + 1)` lies in the first, so
`(2 * M, 2 * M + 2)` is a twin pair of practical numbers of size at least `2 * 3 ^ b`.
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A positive integer `n` is *practical* if every `m ≤ n` can be written as a sum of
distinct divisors of `n`. -/

lemma repr_pow2 (k : ℕ) : ∀ m < 2 ^ (k + 1), ∃ S ⊆ pow2set k, ∑ d ∈ S, d = m := by
  induction k with
  | zero =>
    intro m hm
    norm_num at hm
    interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp [pow2set], by simp⟩
  | succ k ih =>
    intro m hm
    by_cases h : m < 2 ^ (k + 1)
    · obtain ⟨S, hS, hsum⟩ := ih m h
      exact ⟨S, hS.trans pow2set_mono, hsum⟩
    · push_neg at h
      have hsplit : (2 : ℕ) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      have h1 : m - 2 ^ (k + 1) < 2 ^ (k + 1) := by omega
      obtain ⟨S, hS, hsum⟩ := ih _ h1
      have hnot : 2 ^ (k + 1) ∉ S := by
        intro hmem
        have h2 := mem_pow2set_le (hS hmem)
        have h3 : (2 : ℕ) ^ k < 2 ^ (k + 1) := by
          exact Nat.pow_lt_pow_right one_lt_two (by omega)
        omega
      refine ⟨insert (2 ^ (k + 1)) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [pow2set, Finset.mem_image, Finset.mem_range]
          exact ⟨k + 1, by omega, rfl⟩
        · exact pow2set_mono (hS hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega

/-! ### The divisors of `2 * 3 ^ b` -/

/-- The divisors `3^j` and `2 * 3^j` for `j ≤ b`. -/
