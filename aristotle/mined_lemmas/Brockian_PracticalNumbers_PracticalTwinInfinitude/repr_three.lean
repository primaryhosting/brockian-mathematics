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

lemma repr_three (b : ℕ) : ∀ m ≤ sigma3 b, ∃ S ⊆ three2set b, ∑ d ∈ S, d = m := by
  induction b with
  | zero =>
    intro m hm
    simp only [sigma3] at hm
    have h2 : three2set 0 = {1, 2} := by decide
    interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by rw [h2]; intro x hx; simp at hx; simp [hx], by simp⟩
    · exact ⟨{2}, by rw [h2]; intro x hx; simp at hx; simp [hx], by simp⟩
    · exact ⟨{1, 2}, by rw [h2], by decide⟩
  | succ b ih =>
    intro m hm
    have hσ := three_pow_le_sigma3 b
    have hpow : (3 : ℕ) ^ (b + 2) = 3 * 3 ^ (b + 1) := by ring
    simp only [sigma3] at hm
    by_cases h1 : m ≤ sigma3 b
    · obtain ⟨S, hS, hsum⟩ := ih m h1
      exact ⟨S, hS.trans three2set_mono, hsum⟩
    push_neg at h1
    by_cases h2 : m ≤ sigma3 b + 3 ^ (b + 1)
    · -- use the divisor `3 ^ (b+1)`
      obtain ⟨S, hS, hsum⟩ := ih (m - 3 ^ (b + 1)) (by omega)
      have hnot : (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => three_pow_succ_notMem (hS hmem)
      refine ⟨insert (3 ^ (b + 1)) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
          exact Or.inl ⟨b + 1, by omega, rfl⟩
        · exact three2set_mono (hS hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega
    push_neg at h2
    by_cases h3 : m ≤ sigma3 b + 2 * 3 ^ (b + 1)
    · -- use the divisor `2 * 3 ^ (b+1)`
      obtain ⟨S, hS, hsum⟩ := ih (m - 2 * 3 ^ (b + 1)) (by omega)
      have hnot : 2 * (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => two_mul_three_pow_succ_notMem (hS hmem)
      refine ⟨insert (2 * 3 ^ (b + 1)) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
          exact Or.inr ⟨b + 1, by omega, rfl⟩
        · exact three2set_mono (hS hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega
    push_neg at h3
    -- use both `3 ^ (b+1)` and `2 * 3 ^ (b+1)`
    obtain ⟨S, hS, hsum⟩ := ih (m - 3 * 3 ^ (b + 1)) (by omega)
    have hnot1 : (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => three_pow_succ_notMem (hS hmem)
    have hnot2 : 2 * (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => two_mul_three_pow_succ_notMem (hS hmem)
    have hpos : 0 < (3 : ℕ) ^ (b + 1) := Nat.pow_pos (by norm_num) _
    have hne : (3 : ℕ) ^ (b + 1) ≠ 2 * 3 ^ (b + 1) := by omega
    refine ⟨insert (3 ^ (b + 1)) (insert (2 * 3 ^ (b + 1)) S), ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        exact Or.inl ⟨b + 1, by omega, rfl⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨b + 1, by omega, rfl⟩
      · exact three2set_mono (hS hx)
    · rw [Finset.sum_insert (by simp [hne, hnot1]), Finset.sum_insert hnot2, hsum]
      omega

/-! ### The gluing lemma -/

/-- If `D` is a set of divisors of `c` rich enough to represent all `A ≤ c` and all `B < t`,
and `t * d ≠ d'` for all `d, d' ∈ D`, then `c * t` is practical. -/
