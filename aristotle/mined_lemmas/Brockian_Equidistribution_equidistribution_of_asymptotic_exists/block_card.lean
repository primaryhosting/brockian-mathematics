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
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/

lemma block_card (m : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((((Finset.range (m + 1)).filter (fun k => u (T m + k) ∈ Set.Ico a b)).card : ℝ)) -
      (b - a) * ((m : ℝ) + 1)| ≤ 1 := by
  have hrw : ((Finset.range (m + 1)).filter (fun k => u (T m + k) ∈ Set.Ico a b)) =
      ((Finset.range (m + 1)).filter (fun k : ℕ => ((k : ℝ) / ((m : ℝ) + 1)) ∈ Set.Ico a b)) := by
    apply Finset.filter_congr
    intro k hk
    rw [u_block m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [hrw]
  have h := arith_block_card (m + 1) (Nat.succ_pos m) a b ha hab hb
  push_cast at h
  exact h

