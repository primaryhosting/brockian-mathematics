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

lemma bitRev_injOn (k : ℕ) {m n : ℕ} (hm : m < 2 ^ k) (hn : n < 2 ^ k)
    (h : bitRev k m = bitRev k n) : m = n := by
  induction k generalizing m n with
  | zero => simp at hm hn; omega
  | succ k ih =>
    simp only [bitRev] at h
    have b1 := bitRev_lt k (m / 2)
    have b2 := bitRev_lt k (n / 2)
    have hm2 : m % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have hn2 : n % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have hbit1 : m % 2 = n % 2 := by nlinarith
    rw [hbit1] at h
    have hbit2 : bitRev k (m / 2) = bitRev k (n / 2) := by omega
    have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hdm : m / 2 < 2 ^ k := by omega
    have hdn : n / 2 < 2 ^ k := by omega
    have := ih hdm hdn hbit2
    omega

