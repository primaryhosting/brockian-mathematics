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

lemma blockCnt_bound (m : ℕ) (hm : 0 < m) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((blockCnt a b m : ℕ) : ℝ) - (m : ℝ) * (b - a)| ≤ 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hA0 : (0 : ℝ) ≤ a * m := by positivity
  have hB0 : (0 : ℝ) ≤ b * m := by nlinarith
  have hA1 : a * m ≤ (⌈a * m⌉₊ : ℝ) := Nat.le_ceil _
  have hA2 : (⌈a * m⌉₊ : ℝ) < a * m + 1 := Nat.ceil_lt_add_one hA0
  have hB1 : b * m ≤ (⌈b * m⌉₊ : ℝ) := Nat.le_ceil _
  have hB2 : (⌈b * m⌉₊ : ℝ) < b * m + 1 := Nat.ceil_lt_add_one hB0
  have hAB : ⌈a * m⌉₊ ≤ ⌈b * m⌉₊ := Nat.ceil_le_ceil (by nlinarith)
  rw [blockCnt_eq a b m hm hb]
  have hcast : ((⌈b * m⌉₊ - ⌈a * m⌉₊ : ℕ) : ℝ) = (⌈b * m⌉₊ : ℝ) - (⌈a * m⌉₊ : ℝ) :=
    Nat.cast_sub hAB
  rw [hcast, abs_le]
  constructor <;> nlinarith

