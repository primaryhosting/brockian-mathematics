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

lemma card_filter_mod_mem (m N : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : ∀ r ∈ S, r < m) :
    |(#{n ∈ Finset.range N | n % m ∈ S} : ℝ) - S.card * N / m| ≤ S.card := by
  have hbi : {n ∈ Finset.range N | n % m ∈ S}
      = S.biUnion (fun r => {n ∈ Finset.range N | n % m = r}) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x % m, h2, h1, rfl⟩
    · rintro ⟨r, hr, h1, h2⟩; exact ⟨h1, h2 ▸ hr⟩
  have hcard : #{n ∈ Finset.range N | n % m ∈ S}
      = ∑ r ∈ S, #{n ∈ Finset.range N | n % m = r} := by
    rw [hbi, Finset.card_biUnion]
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro x ⟨_, rfl⟩ ⟨_, h⟩
    exact hab h
  have key : ((#{n ∈ Finset.range N | n % m ∈ S} : ℕ) : ℝ) - S.card * N / m
      = ∑ r ∈ S, ((#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m) := by
    rw [Finset.sum_sub_distrib, hcard]
    push_cast
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [key]
  calc |∑ r ∈ S, ((#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m)|
      ≤ ∑ r ∈ S, |((#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum (fun r hr => card_filter_mod_eq m N r hm (hS r hr))
    _ = S.card := by simp

