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

lemma tendsto_cnt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Tendsto (fun N : ℕ => (cnt x N : ℝ) / N) atTop (𝓝 x) := by
  rcases eq_or_lt_of_le hx1 with rfl | hlt
  · have hev : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] fun N : ℕ => (cnt 1 N : ℝ) / N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [cnt_one]
      field_simp
    exact tendsto_const_nhds.congr' hev
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((1 : ℝ) / 2) ^ k < ε / 2 :=
      exists_pow_lt_of_lt_one (by linarith) (by norm_num)
    obtain ⟨M, hM⟩ := exists_nat_gt ((2 : ℝ) ^ k * 2 / ε)
    refine ⟨max M 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_right M 1) hN
    have hNM : (M : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left M 1) hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have hbound := cnt_bound x hx0 hlt k N
    have hkk : (1 : ℝ) / 2 ^ k < ε / 2 := by
      rw [div_pow] at hk; simpa using hk
    have h2k : (2 : ℝ) ^ k / N < ε / 2 := by
      rw [div_lt_iff₀ hNpos]
      have h0 : (2 : ℝ) ^ k * 2 / ε < N := lt_of_lt_of_le hM hNM
      rw [div_lt_iff₀ hε] at h0
      linarith
    rw [Real.dist_eq]
    have heq : (cnt x N : ℝ) / N - x = ((cnt x N : ℝ) - x * N) / N := by field_simp
    rw [heq, abs_div, abs_of_pos hNpos]
    calc |(cnt x N : ℝ) - x * N| / N ≤ ((N : ℝ) / 2 ^ k + 2 ^ k) / N := by gcongr
      _ = 1 / 2 ^ k + 2 ^ k / N := by field_simp
      _ < ε := by linarith

