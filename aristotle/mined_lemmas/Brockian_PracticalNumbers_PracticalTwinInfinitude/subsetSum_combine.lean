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

lemma subsetSum_combine {D : Finset ℕ} {w t : ℕ}
    (hcomp : ∀ r ≤ ∑ d ∈ D, d, SubsetSum D r) (hw : 1 ≤ w) (hwS : w ≤ (∑ d ∈ D, d) + 1)
    (hcoll : ∀ d ∈ D, ∀ d' ∈ D, w * d ≠ d') (ht : t ≤ w * ∑ d ∈ D, d) :
    SubsetSum (D ∪ D.image (fun d => w * d)) t := by
  have hw0 : 0 < w := hw
  obtain ⟨S1, hS1, hq⟩ := hcomp (t / w) (by
    calc t / w ≤ (w * ∑ d ∈ D, d) / w := Nat.div_le_div_right ht
      _ = ∑ d ∈ D, d := Nat.mul_div_cancel_left _ hw0)
  obtain ⟨S2, hS2, hr⟩ := hcomp (t % w) (by
    have := Nat.mod_lt t hw0
    omega)
  have hinj : ∀ x ∈ S1, ∀ y ∈ S1, w * x = w * y → x = y := fun x _ y _ h =>
    Nat.eq_of_mul_eq_mul_left hw0 h
  have hdisj : Disjoint S2 (S1.image (fun d => w * d)) := by
    rw [Finset.disjoint_right]
    intro x hx hx2
    obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hx
    exact hcoll d (hS1 hd) x (hS2 hx2) hdx
  refine ⟨S2 ∪ S1.image (fun d => w * d),
    Finset.union_subset_union hS2 (Finset.image_subset_image hS1), ?_⟩
  rw [Finset.sum_union hdisj, Finset.sum_image hinj, hr, ← Finset.mul_sum, hq]
  exact Nat.mod_add_div t w

/-- Practicality from a complete set of divisors. -/
