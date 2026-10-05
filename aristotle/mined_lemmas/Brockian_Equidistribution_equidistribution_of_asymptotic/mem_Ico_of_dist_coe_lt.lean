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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic

This file proves **Weyl's criterion**: if a real sequence `x` satisfies the asymptotic
exponential-sum estimate `∑_{n < N} e(h * xₙ) = o(N)` for every nonzero integer `h`, then `x`
is equidistributed modulo one, i.e. for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
indices `n < N` with `Int.fract (xₙ) ∈ [a, b)` tends to `b - a`.
-/

open Filter Finset MeasureTheory Metric Set Submodule
open scoped BigOperators Real Topology

namespace Brockian.Equidistribution

noncomputable section

/-- The image of a real sequence in the circle `ℝ / ℤ`. -/

lemma mem_Ico_of_dist_coe_lt {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hd : dist ((y : AddCircle (1 : ℝ))) (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) < (b - a) / 2) :
    y ∈ Set.Ico a b := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq] at hd
  set k : ℤ := round (y - (a + b) / 2) with hk
  rw [abs_lt] at hd
  obtain ⟨h1, h2⟩ := hd
  have hk0 : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      linarith
    · have hge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
      linarith
  rw [hk0] at h1 h2
  simp only [Int.cast_zero, sub_zero] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Weyl's criterion.**  If the exponential sums `∑_{n < N} e(h xₙ)` are `o(N)` for every
nonzero integer `h`, then the sequence `x` is equidistributed modulo one. -/
