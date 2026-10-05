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

lemma practical_two_pow_mul_odd {k u : ℕ} (hu : Odd u) (hle : u ≤ 2 ^ (k + 1)) :
    Practical (2 ^ k * u) := by
  have hupos : 0 < u := hu.pos
  rcases eq_or_lt_of_le hupos with h1 | h1
  · -- `u = 1`: a power of two
    have hu1 : u = 1 := by omega
    subst hu1
    rw [mul_one]
    refine practical_of_subset (Nat.pow_pos (by norm_num) k) (pow2set k) ?_ ?_
    · intro d hd
      rw [Nat.mem_divisors]
      exact ⟨mem_pow2set_dvd hd, by positivity⟩
    · intro m hm
      exact repr_pow2 k m (by
        have : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
        omega)
  · -- `u > 1`
    have hcross : ∀ d ∈ pow2set k, ∀ d' ∈ pow2set k, u * d ≠ d' := by
      intro d hd d' hd' heq
      simp only [pow2set, Finset.mem_image, Finset.mem_range] at hd hd'
      obtain ⟨i, _, rfl⟩ := hd
      obtain ⟨j, _, rfl⟩ := hd'
      have hdvd : u ∣ 2 ^ j := ⟨2 ^ i, by omega⟩
      obtain ⟨m, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h1
      · have : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 (by omega)
        rw [Nat.odd_iff] at hu
        omega
    have := practical_glue (c := 2 ^ k) (t := u) (pow2set k)
      (Nat.pow_pos (by norm_num) k) hupos
      (fun d hd => mem_pow2set_dvd hd)
      (fun A hA => repr_pow2 k A (by
        have : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
        omega))
      (fun B hB => repr_pow2 k B (by omega))
      hcross
    exact this

/-- If `t` is odd, prime to `3`, and `t ≤ 3 ^ b`, then `2 * 3 ^ b * t` is practical. -/
