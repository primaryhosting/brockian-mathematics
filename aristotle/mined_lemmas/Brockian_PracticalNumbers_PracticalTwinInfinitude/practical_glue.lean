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

lemma practical_glue {c t : ℕ} (D : Finset ℕ) (hc : 0 < c) (ht : 0 < t)
    (hD : ∀ d ∈ D, d ∣ c)
    (hA : ∀ A ≤ c, ∃ S ⊆ D, ∑ d ∈ S, d = A)
    (hB : ∀ B < t, ∃ S ⊆ D, ∑ d ∈ S, d = B)
    (hcross : ∀ d ∈ D, ∀ d' ∈ D, t * d ≠ d') :
    Practical (c * t) := by
  have hct : 0 < c * t := Nat.mul_pos hc ht
  refine ⟨hct, fun m hm => ?_⟩
  have hAle : m / t ≤ c := by
    have h := Nat.div_le_div_right (c := t) hm
    rwa [Nat.mul_div_cancel _ ht] at h
  obtain ⟨S1, hS1, hsum1⟩ := hA (m / t) hAle
  obtain ⟨S2, hS2, hsum2⟩ := hB (m % t) (Nat.mod_lt _ ht)
  have hinj : Set.InjOn (fun d => t * d) S1 := by
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left ht h
  have hdisj : Disjoint (S1.image (fun d => t * d)) S2 := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact hcross d (hS1 hd) _ (hS2 hx2) rfl
  refine ⟨(S1.image (fun d => t * d)) ∪ S2, ?_, ?_⟩
  · intro x hx
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [Finset.mem_image] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      rw [mul_comm c t]
      exact Nat.mul_dvd_mul_left t (hD d (hS1 hd))
    · exact Dvd.dvd.mul_right (hD x (hS2 hx)) t
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj, ← Finset.mul_sum, hsum1, hsum2]
    exact Nat.div_add_mod m t

/-! ### Two families of practical numbers -/

/-- If `u` is odd and `u ≤ 2 ^ (k+1)` then `2 ^ k * u` is practical. -/
