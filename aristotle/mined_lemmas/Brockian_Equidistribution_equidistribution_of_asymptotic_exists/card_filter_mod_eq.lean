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

lemma card_filter_mod_eq (m N r : ℕ) (hm : 0 < m) (hr : r < m) :
    |(#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m| ≤ 1 := by
  have hset : {n ∈ Finset.range N | n % m = r} = {x ∈ Finset.range N | x ≡ r [MOD m]} := by
    apply Finset.filter_congr
    intro x _
    simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
  set c : ℕ := #{n ∈ Finset.range N | n % m = r} with hc
  have hceil : (c : ℤ) = ⌈((N : ℚ) - r) / m⌉ := by
    have := Nat.count_modEq_card_eq_ceil N hm r
    rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hr, ← hset] at this
    exact_mod_cast this
  have h1 : ((N : ℚ) - r) / m ≤ (c : ℚ) := by
    rw [show ((c : ℚ)) = ((c : ℤ) : ℚ) by push_cast; ring, hceil]
    exact_mod_cast Int.le_ceil (((N : ℚ) - r) / m)
  have h2 : (c : ℚ) < ((N : ℚ) - r) / m + 1 := by
    rw [show ((c : ℚ)) = ((c : ℤ) : ℚ) by push_cast; ring, hceil]
    exact_mod_cast Int.ceil_lt_add_one (((N : ℚ) - r) / m)
  have h1' : ((N : ℝ) - r) / m ≤ (c : ℝ) := by exact_mod_cast h1
  have h2' : (c : ℝ) < ((N : ℝ) - r) / m + 1 := by exact_mod_cast h2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR2 : (r : ℝ) < m := by exact_mod_cast hr
  have hsplit : ((N : ℝ) - r) / m = N / m - r / m := by field_simp
  have hlt : (r : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact hrR2
  have hge : (0 : ℝ) ≤ (r : ℝ) / m := by positivity
  rw [hsplit] at h1' h2'
  rw [abs_le]
  constructor <;> linarith

