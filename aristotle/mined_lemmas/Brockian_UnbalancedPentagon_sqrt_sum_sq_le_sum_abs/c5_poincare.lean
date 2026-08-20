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

theorem c5_poincare (y : Fin 5 → ℝ) :
    2 * g5 * (∑ i, (y i) ^ 2) ≤ (∑ i, (y i - y (i + 1)) ^ 2) + (2 * g5 / 5) * (∑ i, y i) ^ 2 := by
  have hs0 : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have H := c5_sos (Real.sqrt 5) (y 0) (y 1) (y 2) (y 3) (y 4) hs hs0
  simp only [Fin.sum_univ_five, Fin5.add_one_0, Fin5.add_one_1, Fin5.add_one_2,
    Fin5.add_one_3, Fin5.add_one_4, g5]
  linarith [H]

/-- Centered form: if `∑ y i = 0` then `2 g₅ ∑ y i ^ 2 ≤ ∑ (y i - y (i+1))^2`. -/
