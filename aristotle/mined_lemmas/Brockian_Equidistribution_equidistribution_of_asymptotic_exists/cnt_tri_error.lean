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

lemma cnt_tri_error (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (K : ℕ) :
    |(cnt x (tri K) : ℝ) - x * tri K| ≤ K := by
  rw [cnt_tri x hx1 K, tri_cast K]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range K, ((⌈((k : ℝ) + 1) * x⌉₊ : ℝ) - x * ((k : ℝ) + 1))|
      ≤ ∑ k ∈ Finset.range K, |(⌈((k : ℝ) + 1) * x⌉₊ : ℝ) - x * ((k : ℝ) + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hnn : (0 : ℝ) ≤ ((k : ℝ) + 1) * x := by positivity
        have h := ceil_sub_le_one (((k : ℝ) + 1) * x) hnn
        rw [show x * ((k : ℝ) + 1) = ((k : ℝ) + 1) * x by ring]
        exact h
    _ = K := by simp

