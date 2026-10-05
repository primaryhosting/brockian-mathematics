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

This file constructs an explicit sequence in `[0, 1)` whose empirical distribution is
asymptotically the uniform one: for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
the first `N` terms lying in `[a, b)` converges to `b - a`.

The construction is the "triangular block" sequence
`0/1 ; 0/2, 1/2 ; 0/3, 1/3, 2/3 ; 0/4, …` .
-/

open Filter Topology

namespace Brockian.Equidistribution

/-- Triangular numbers: `tri k = 0 + 1 + ⋯ + k`. -/

lemma cnt_bound (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N K : ℕ)
    (h1 : tri K ≤ N) (h2 : N ≤ tri (K + 1)) :
    |((cnt a b N : ℕ) : ℝ) - (N : ℝ) * (b - a)| ≤ 3 * (K : ℝ) + 3 := by
  have hlow : cnt a b (tri K) ≤ cnt a b N := cnt_mono a b h1
  have hhigh : cnt a b N ≤ cnt a b (tri (K + 1)) := cnt_mono a b h2
  have hstep : cnt a b (tri (K + 1)) = cnt a b (tri K) + blockCnt a b (K + 1) :=
    cnt_succ_block a b K
  have hba0 : 0 ≤ b - a := by linarith
  have hba1 : b - a ≤ 1 := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hblock : (blockCnt a b (K + 1) : ℝ) ≤ (K : ℝ) + 2 := by
    have hbb := blockCnt_bound a b (K + 1) (Nat.succ_pos K) ha hab hb
    rw [abs_le] at hbb
    have h := hbb.2
    push_cast at h
    nlinarith
  have htri : (tri K : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
  have htri2 : (N : ℝ) ≤ (tri K : ℝ) + ((K : ℝ) + 1) := by
    have hn : N ≤ tri K + (K + 1) := by rw [tri_succ] at h2; omega
    exact_mod_cast hn
  have hIH := cnt_tri_bound a b ha hab hb K
  rw [abs_le] at hIH ⊢
  have hlowR : ((cnt a b (tri K) : ℕ) : ℝ) ≤ ((cnt a b N : ℕ) : ℝ) := by exact_mod_cast hlow
  have hhighR : ((cnt a b N : ℕ) : ℝ)
      ≤ ((cnt a b (tri K) : ℕ) : ℝ) + (blockCnt a b (K + 1) : ℝ) := by
    have hle : cnt a b N ≤ cnt a b (tri K) + blockCnt a b (K + 1) := by omega
    exact_mod_cast hle
  constructor <;> nlinarith [hIH.1, hIH.2]

end Counting

