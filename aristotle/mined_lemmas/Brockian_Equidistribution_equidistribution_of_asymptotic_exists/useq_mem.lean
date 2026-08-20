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

lemma useq_mem (n : ℕ) : useq n ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := blk_spec n
  have hm : n - tri (blk n) ≤ blk n := by rw [tri_succ] at h2; omega
  have hpos : (0 : ℝ) < (blk n : ℝ) + 1 := by positivity
  rw [Set.mem_Ico, useq]
  constructor
  · exact div_nonneg (by positivity) (le_of_lt hpos)
  · rw [div_lt_one hpos]
    have : ((n - tri (blk n) : ℕ) : ℝ) ≤ (blk n : ℝ) := by exact_mod_cast hm
    linarith

/-- The counting function: the number of `n < N` with `useq n < x`. -/
