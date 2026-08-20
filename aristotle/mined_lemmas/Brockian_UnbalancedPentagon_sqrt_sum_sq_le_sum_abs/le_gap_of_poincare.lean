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

theorem le_gap_of_poincare (hm : ∀ i, 0 < m i) {c : ℝ}
    (h : ∀ y : Fin 5 → ℝ, Ctr m y = 0 → c * Ms m y ≤ En m y) : c ≤ gap m := by
  rw [gap]
  have hsec : sec (Q m) (perron m) ≤ 1 - c := by
    refine sec_le_of hm ?_
    intro x hx hp
    have hxy : (fun i => perron m i * (x i / perron m i)) = x := perron_mul_div hm x
    have hMs : Ms m (fun i => x i / perron m i) = 1 := by
      rw [← dot_self_y hm (fun i => x i / perron m i), hxy]; exact hx
    have hCtr : Ctr m (fun i => x i / perron m i) = 0 := by
      rw [← dot_perron_y hm (fun i => x i / perron m i), hxy]; exact hp
    have hh := h _ hCtr
    rw [hMs, mul_one] at hh
    rw [rayleigh_eq_of_unit hm hx]
    linarith
  linarith

