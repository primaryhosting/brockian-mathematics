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

lemma practical_of_combine {m w : ℕ} (hm0 : 0 < m) (D : Finset ℕ) (hD : ∀ d ∈ D, d ∣ m)
    (hm : m ∈ D) (hcomp : ∀ t ≤ ∑ d ∈ D, d, SubsetSum D t) (hw : 1 ≤ w)
    (hwS : w ≤ (∑ d ∈ D, d) + 1) (hcoll : ∀ d ∈ D, ∀ d' ∈ D, w * d ≠ d') :
    Practical (w * m) := by
  have hmS : m ≤ ∑ d ∈ D, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hm
  have hpos : 0 < w * m := Nat.mul_pos hw hm0
  refine practical_of_complete hpos (D ∪ D.image (fun d => w * d)) ?_ ?_
  · intro x hx
    rw [Finset.mem_union] at hx
    refine Nat.mem_divisors.mpr ⟨?_, hpos.ne'⟩
    rcases hx with hx | hx
    · exact (hD x hx).trans (dvd_mul_left m w)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact Nat.mul_dvd_mul_left w (hD d hd)
  · intro t ht
    exact subsetSum_combine hcomp hw hwS hcoll (ht.trans (Nat.mul_le_mul_left w hmS))

/-! ## Powers of two -/

/-- `P2 A = {1, 2, 4, …, 2^A}`. -/
