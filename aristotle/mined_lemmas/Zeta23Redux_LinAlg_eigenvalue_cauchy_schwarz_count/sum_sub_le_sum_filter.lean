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
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- The total "excess above `theta`" is at most the sum of the eigenvalues that exceed
`theta`: the indices below the threshold contribute a nonpositive amount, and subtracting
`n * theta` (with `theta ≥ 0`) only decreases the sum. -/

theorem sum_sub_le_sum_filter
    {d : ℕ} (ev : Fin d → ℝ) {theta : ℝ} (htheta : 0 ≤ theta) :
    (∑ i, ev i) - theta * d
      ≤ ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), ev i := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hs
  have hsplit :
      ∑ i ∈ s, (ev i - theta) + ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i),
        (ev i - theta) = ∑ i : Fin d, (ev i - theta) := by
    rw [hs]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ _ _
  have htot : ∑ i : Fin d, (ev i - theta) = (∑ i, ev i) - theta * d := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [mul_comm]
  have hneg : ∑ i ∈ Finset.univ.filter (fun i => ¬ theta < ev i), (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_filter, not_lt] at hi
    linarith [hi.2]
  have hfirst : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
    rw [Finset.sum_sub_distrib]
    have : (0 : ℝ) ≤ ∑ _i ∈ s, theta := Finset.sum_nonneg fun _ _ => htheta
    linarith
  linarith [hsplit, htot]

/-- Restricting the sum of squares to the above-threshold indices only decreases it. -/
