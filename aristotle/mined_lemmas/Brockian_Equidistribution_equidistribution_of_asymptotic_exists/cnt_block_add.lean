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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian.Equidistribution

/-- A sequence `u : ℕ → ℝ` is *asymptotically equidistributed mod 1* if for every
subinterval `[a, b) ⊆ [0, 1]` the asymptotic density of the set of indices `n` with
`Int.fract (u n) ∈ [a, b)` exists and equals the length `b - a` of the interval. -/

lemma cnt_block_add (x : ℝ) (K : ℕ) :
    ∀ m ≤ K + 1, cnt x (tri K + m) = cnt x (tri K) + min m ⌈((K : ℝ) + 1) * x⌉₊ := by
  intro m hm
  induction m with
  | zero => simp
  | succ p ih =>
      have hp : p ≤ K := by omega
      have ihp := ih (by omega)
      have hstep : cnt x (tri K + (p + 1))
          = cnt x (tri K + p) + if useq (tri K + p) < x then 1 else 0 := by
        have hrw : tri K + (p + 1) = (tri K + p) + 1 := by omega
        rw [hrw, cnt_succ]
      rw [hstep, ihp, useq_block K p hp]
      by_cases h : (p : ℝ) / ((K : ℝ) + 1) < x
      · have hlt : p < ⌈((K : ℝ) + 1) * x⌉₊ := (lt_iff_lt_ceil x K p).mp h
        simp only [h, if_true]
        omega
      · have hlt : ¬ (p < ⌈((K : ℝ) + 1) * x⌉₊) := fun hc =>
          h ((lt_iff_lt_ceil x K p).mpr hc)
        simp only [h, if_false]
        omega

