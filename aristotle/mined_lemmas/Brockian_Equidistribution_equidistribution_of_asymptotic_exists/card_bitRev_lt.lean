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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The named hypothesis is discharged unconditionally by exhibiting an explicit equidistributed
sequence: the base-`2` van der Corput sequence `vdc`, defined by `vdc n = ((n % 2) + vdc (n / 2))/2`.
Writing `bitRev k n` for the reversal of the lowest `k` binary digits of `n`, one has
`vdc n = (bitRev k n + vdc (n / 2 ^ k)) / 2 ^ k`, so `vdc n` lies in the dyadic interval
`[bitRev k n / 2 ^ k, (bitRev k n + 1) / 2 ^ k)`. Since `bitRev k` is a bijection of
`{0, …, 2 ^ k - 1}` depending only on `n % 2 ^ k`, counting the visits to a dyadic interval
reduces to counting an arithmetic progression, which is handled by the Mathlib lemma
`Nat.count_modEq_card_eq_ceil`. Sandwiching an arbitrary interval between dyadic ones then gives
the discrepancy bound `|#{n < N : vdc n < x} - x * N| ≤ N / 2 ^ k + 2 ^ k`, whence equidistribution.
-/

open Filter Finset
open scoped Topology

namespace Brockian.Equidistribution

/-- A sequence `u : ℕ → ℝ` is equidistributed modulo `1` when, for every subinterval
`[a, b) ⊆ [0, 1)`, the asymptotic frequency with which the fractional parts `Int.fract (u n)`
land in `[a, b)` exists and equals the length `b - a` of the interval. -/

lemma card_bitRev_lt (k t : ℕ) (ht : t ≤ 2 ^ k) :
    #{r ∈ Finset.range (2 ^ k) | bitRev k r < t} = t := by
  set S := {r ∈ Finset.range (2 ^ k) | bitRev k r < t} with hSdef
  have hinj : Set.InjOn (bitRev k) (S : Set ℕ) := by
    intro a ha b hb hab
    simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb
    exact bitRev_injOn k ha.1 hb.1 hab
  have himg : S.image (bitRev k) = Finset.range t := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range, hSdef, Finset.mem_filter]
    constructor
    · rintro ⟨r, ⟨_, hr2⟩, rfl⟩; exact hr2
    · intro hj
      have hsurj : (Finset.range (2 ^ k)).image (bitRev k) = Finset.range (2 ^ k) := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
          obtain ⟨r, _, rfl⟩ := hx
          exact bitRev_lt k r
        · rw [Finset.card_image_of_injOn, Finset.card_range]
          intro a ha b hb hab
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          exact bitRev_injOn k ha hb hab
      have hj2 : j ∈ Finset.range (2 ^ k) := Finset.mem_range.mpr (lt_of_lt_of_le hj ht)
      rw [← hsurj] at hj2
      simp only [Finset.mem_image, Finset.mem_range] at hj2
      obtain ⟨r, hr, hrj⟩ := hj2
      exact ⟨r, ⟨hr, by rw [hrj]; exact hj⟩, hrj⟩
  calc S.card = (S.image (bitRev k)).card := (Finset.card_image_of_injOn hinj).symm
    _ = t := by rw [himg, Finset.card_range]

