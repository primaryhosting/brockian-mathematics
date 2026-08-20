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
# Equidistribution: reduction from continuous test functions to BV (indicator) test functions

This file contains the classical "bounded variation reduction" step in the theory of
equidistribution modulo one: if a sequence `x : ℕ → ℝ` is equidistributed mod `1` in Weyl's
sense (Cesàro averages of *continuous* `1`-periodic test functions converge to the mean of the
test function), then the counting density of the "configurations" `n ↦ Int.fract (x n)` lying in
a subinterval `[a, b) ⊆ [0, 1)` converges to the length `b - a`.

The indicator of an interval is the basic example of a function of bounded variation which is not
continuous, so the content of the main theorem is exactly that the class of admissible test
functions may be enlarged from continuous functions to such BV functions.

The main result is `Brockian.EquidistributionBVReduction.configCount_density_of_BV`; it is
unconditional apart from the (necessary) equidistribution hypothesis on the sequence itself.
-/

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma configCount_partition (x : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    configCount x 0 a N + configCount x a b N + configCount x b 1 N = N := by
  classical
  simp only [configCount, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (g := fun _ => 1) ?_, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_range]
  intro n _
  have h0 : 0 ≤ Int.fract (x n) := Int.fract_nonneg _
  have h1 : Int.fract (x n) < 1 := Int.fract_lt_one _
  rcases lt_or_ge (Int.fract (x n)) a with h | h
  · have hna : ¬ (a ≤ Int.fract (x n)) := not_le.2 h
    have hb' : ¬ (b ≤ Int.fract (x n)) := fun hc => hna (le_trans hab hc)
    simp [Set.mem_Ico, h0, h, hna, hb']
  · rcases lt_or_ge (Int.fract (x n)) b with h' | h'
    · have hb' : ¬ (b ≤ Int.fract (x n)) := not_le.2 h'
      simp [Set.mem_Ico, h0, h, h', hb', not_lt.2 h]
    · simp [Set.mem_Ico, h0, h1, h, h', not_lt.2 h, not_lt.2 h']

/-- The key lower bound: asymptotically, the count of configurations in `[a, b)` is at least
`(b - a - ε) N`. -/
