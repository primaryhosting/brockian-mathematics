import Brockian.Fin5
import Brockian.Defs
import Brockian.Rayleigh
import Brockian.Gap
import Brockian.Poincare
import Brockian.LowerBound
import Brockian.LtOne
import Brockian.Perturb
import Brockian.LimitMatrices
import Brockian.FamilyDefs
import Brockian.LimitA
import Brockian.LimitB
import Brockian.GapLimits
import Brockian.Range
import Brockian.Spectrum
import Brockian.OpNorm
import Brockian.MinMax
import Brockian.UnbalancedPentagonLimits

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

import Brockian.LimitA
import Brockian.LimitB
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator-norm form of the two matrix limits

The entrywise `ℓ¹` norm `nrm1` dominates the `ℓ²` operator norm of a `5 × 5` real matrix
(`opNorm_le_nrm1`).  Consequently the entrywise convergences `Qa_tendsto_Qmin` and
`Qb_tendsto_Qmax` upgrade to convergence in the operator norm.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Finset Filter Topology
open scoped Matrix.Norms.L2Operator

/-- `√(∑ |wᵢ|²) ≤ ∑ |wᵢ|`. -/

theorem weighted_poincare (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ) (hC : Ctr m y = 0) :
    g5 * (mmin m) ^ 2 / (mmax m) ^ 2 * Ms m y ≤ En m y := by
  have hmin := mmin_pos hm
  have hmax := mmax_pos hm
  set c : ℝ := (∑ i, y i) / 5 with hcdef
  set z : Fin 5 → ℝ := fun i => y i - c with hz
  -- (1) `z` is centered
  have h1 : (∑ i, z i) = 0 := by
    simp only [hz, hcdef, Fin.sum_univ_five]
    ring
  -- (2) the energy only depends on differences
  have h2 : En m z = En m y := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hz]; ring
  -- (3) conductance lower bound
  have h3 : (mmin m) ^ 2 * (∑ i, (z i - z (i + 1)) ^ 2) ≤ En m z := by
    rw [En, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have ha : mmin m ≤ m i := mmin_le m i
    have hb : mmin m ≤ m (i + 1) := mmin_le m (i + 1)
    have hmul : (mmin m) ^ 2 ≤ m i * m (i + 1) := by nlinarith
    nlinarith [sq_nonneg (z i - z (i + 1))]
  -- (4) Poincaré on `C₅`
  have h4 : 2 * g5 * (∑ i, (z i) ^ 2) ≤ ∑ i, (z i - z (i + 1)) ^ 2 := c5_poincare_centered h1
  -- (5) weight upper bound
  have h5 : Ms m z ≤ 2 * (mmax m) ^ 2 * (∑ i, (z i) ^ 2) := by
    rw [Ms, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have ha : m i ≤ mmax m := le_mmax m i
    have hb : m (i - 1) ≤ mmax m := le_mmax m (i - 1)
    have hc' : m (i + 1) ≤ mmax m := le_mmax m (i + 1)
    have hmi := hm i
    have hwt : wt m i ≤ 2 * (mmax m) ^ 2 := by
      simp only [wt, deg]; nlinarith
    nlinarith [sq_nonneg (z i)]
  -- (6) centering increases the mass
  have h6 : Ms m y ≤ Ms m z := by
    have hCe : wt m 0 * y 0 + wt m 1 * y 1 + wt m 2 * y 2 + wt m 3 * y 3 + wt m 4 * y 4 = 0 := by
      rw [← Ctr_eq]; exact hC
    have hid : Ms m z = Ms m y
        + c ^ 2 * (wt m 0 + wt m 1 + wt m 2 + wt m 3 + wt m 4) := by
      rw [Ms_eq, Ms_eq]
      simp only [hz]
      linear_combination (-2 * c) * hCe
    have hW : 0 ≤ wt m 0 + wt m 1 + wt m 2 + wt m 3 + wt m 4 := by
      have := wt_pos hm 0; have := wt_pos hm 1; have := wt_pos hm 2
      have := wt_pos hm 3; have := wt_pos hm 4
      linarith
    nlinarith [sq_nonneg c]
  -- combine
  set A : ℝ := ∑ i, (z i) ^ 2 with hA
  have hEn : 2 * g5 * (mmin m) ^ 2 * A ≤ En m y := by
    have ht := mul_le_mul_of_nonneg_left h4 (sq_nonneg (mmin m))
    linarith [ht, h3, h2]
  have hMs : Ms m y ≤ 2 * (mmax m) ^ 2 * A := le_trans h6 h5
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have t1 := mul_le_mul_of_nonneg_left hMs (mul_nonneg g5_pos.le (sq_nonneg (mmin m)))
  have t2 := mul_le_mul_of_nonneg_left hEn (sq_nonneg (mmax m))
  nlinarith [t1, t2]

/-- **Target 1.** `g₅ / ρ(m)² ≤ gap m` for every positive fibre-size vector. -/
