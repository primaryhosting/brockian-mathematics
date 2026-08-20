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

lemma blk_spec (n : ℕ) : tri (blk n) ≤ n ∧ n < tri (blk n + 1) := by
  refine ⟨?_, Nat.find_spec (exists_blk n)⟩
  rcases Nat.eq_zero_or_pos (blk n) with h | h
  · simp [h, tri]
  · have hlt : blk n - 1 < Nat.find (exists_blk n) := by
      have : blk n = Nat.find (exists_blk n) := rfl
      omega
    have hmin := Nat.find_min (exists_blk n) hlt
    have h2 : blk n - 1 + 1 = blk n := by omega
    rw [h2] at hmin
    omega

