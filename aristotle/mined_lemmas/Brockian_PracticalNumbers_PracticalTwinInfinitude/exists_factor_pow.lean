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

lemma exists_factor_pow {p : ℕ} (hp : 1 < p) :
    ∀ M : ℕ, 0 < M → ∃ e t : ℕ, M = p ^ e * t ∧ ¬ p ∣ t := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM
    by_cases h : p ∣ M
    · obtain ⟨M', rfl⟩ := h
      have hM' : 0 < M' := by
        rcases Nat.eq_zero_or_pos M' with rfl | h'
        · simp at hM
        · exact h'
      have hlt : M' < p * M' := by nlinarith
      obtain ⟨e, t, he, ht⟩ := ih M' hlt hM'
      exact ⟨e + 1, t, by rw [he]; ring, ht⟩
    · exact ⟨0, M, by simp, h⟩

