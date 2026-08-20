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
# Reduction of equidistribution to bounded-variation test functions

Let `x : ℕ → ℝ` be a sequence.  Assume that for **every** real function `f` of bounded
variation on `[0,1]` the Birkhoff-type averages

`(1/N) * ∑_{n < N} f (Int.fract (x n))`

converge to `∫₀¹ f`.  We show that the sequence `x` is then equidistributed modulo one, and
moreover *uniformly* so: the counting error over intervals `[a,b) ⊆ [0,1]` tends to `0`
uniformly in the endpoints (i.e. the discrepancy of the sequence tends to `0`).

The main statement is `equidistribution_of_BV_uniform`.  It is unconditional: apart from the
assumption on the sequence itself, no auxiliary result is taken as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Brockian

open scoped Classical in
/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem grid_bracket (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ j : ℕ, j + 1 ≤ K ∧ (j:ℝ)/K ≤ t ∧ t ≤ ((j:ℝ)+1)/K := by
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  set j := ⌊t * K⌋₊ with hj
  have hfl : (j:ℝ) ≤ t * K := Nat.floor_le (by positivity)
  have hfl2 : t * K < j + 1 := Nat.lt_floor_add_one _
  by_cases hjK : j + 1 ≤ K
  · exact ⟨j, hjK, by rw [div_le_iff₀ hKR]; exact hfl, by rw [le_div_iff₀ hKR]; exact hfl2.le⟩
  · have hKj : K ≤ j := by omega
    have h1 : (K:ℝ) ≤ t * K := le_trans (by exact_mod_cast hKj) hfl
    have ht : 1 ≤ t := by nlinarith
    have ht' : t = 1 := le_antisymm ht1 ht
    have hcast : ((K - 1 : ℕ) : ℝ) = (K:ℝ) - 1 := by push_cast [Nat.cast_sub hK]; ring
    refine ⟨K - 1, by omega, ?_, ?_⟩
    · rw [hcast, ht', div_le_one hKR]; linarith
    · rw [hcast, ht', le_div_iff₀ hKR]; linarith

/-- Uniform convergence of the cumulative distribution function on `[0,1]`. -/
