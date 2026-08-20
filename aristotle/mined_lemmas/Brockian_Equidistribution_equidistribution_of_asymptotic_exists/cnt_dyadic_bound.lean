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

lemma cnt_dyadic_bound (k t N : ℕ) (ht : t ≤ 2 ^ k) :
    |(cnt ((t : ℝ) / 2 ^ k) N : ℝ) - t * N / 2 ^ k| ≤ 2 ^ k := by
  set S := {r ∈ Finset.range (2 ^ k) | bitRev k r < t} with hSdef
  have hScard : S.card = t := card_bitRev_lt k t ht
  have hset : {n ∈ Finset.range N | bitRev k n < t}
      = {n ∈ Finset.range N | n % 2 ^ k ∈ S} := by
    apply Finset.filter_congr
    intro n _
    simp only [hSdef, Finset.mem_filter, Finset.mem_range, bitRev_mod]
    exact ⟨fun h => ⟨Nat.mod_lt _ (Nat.two_pow_pos k), h⟩, fun h => h.2⟩
  have hmain := card_filter_mod_mem (2 ^ k) N (Nat.two_pow_pos k) S
    (fun r hr => by
      simp only [hSdef, Finset.mem_filter, Finset.mem_range] at hr
      exact hr.1)
  rw [hScard] at hmain
  push_cast at hmain
  rw [cnt_dyadic_eq, hset]
  refine le_trans hmain ?_
  exact_mod_cast ht

