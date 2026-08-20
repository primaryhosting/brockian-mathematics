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

theorem Qmax_charpoly : Qmax.charpoly = ∏ i : Fin 5, (X - C (![1, 0, 0, 0, -1] i : ℝ)) := by
  have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [h]
  have hC : (C (1 / 2 : ℝ)) * 2 = 1 := by
    rw [show (2 : Polynomial ℝ) = C (2 : ℝ) from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  simp [Matrix.charpoly, Matrix.charmatrix, Qmax, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.prod_univ_five, Fin.succAbove]
  have h2' : (C (Real.sqrt 2 * (1 / 2)) : Polynomial ℝ) ^ 2 = C (1 / 2 : ℝ) := by
    rw [← C_pow]
    congr 1
    nlinarith [h2]
  ring_nf
  linear_combination (-2 * (X : Polynomial ℝ) ^ 3) * h2' + (-(X : Polynomial ℝ) ^ 3) * hC

