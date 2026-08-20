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

lemma cnt_tri (x : ℝ) (hx1 : x ≤ 1) (K : ℕ) :
    cnt x (tri K) = ∑ k ∈ Finset.range K, ⌈((k : ℝ) + 1) * x⌉₊ := by
  induction K with
  | zero => simp [tri, cnt]
  | succ K ih =>
      have hceil : ⌈((K : ℝ) + 1) * x⌉₊ ≤ K + 1 := by
        rw [Nat.ceil_le]
        push_cast
        nlinarith
      rw [tri_succ, cnt_block_add x K (K + 1) le_rfl, ih, Finset.sum_range_succ]
      omega

