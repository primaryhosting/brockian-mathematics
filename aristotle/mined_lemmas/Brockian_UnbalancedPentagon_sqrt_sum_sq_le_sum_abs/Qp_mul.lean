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

lemma Qp_mul (hm : ∀ i, 0 < m i) (i j : Fin 5) :
    Q m i j * (perron m i * perron m j) = if Adj i j then m i * m j else 0 := by
  have hdi := deg_pos hm i
  have hdj := deg_pos hm j
  have hmi := hm i
  have hmj := hm j
  by_cases h : Adj i j
  · simp only [Q, perron, if_pos h]
    have hA : (0:ℝ) ≤ m i * m j / (deg m i * deg m j) :=
      div_nonneg (by nlinarith) (by nlinarith)
    have hB : (0:ℝ) ≤ wt m i := (wt_pos hm i).le
    have hC : (0:ℝ) ≤ wt m j := (wt_pos hm j).le
    rw [← Real.sqrt_mul hB, ← Real.sqrt_mul hA]
    have hkey : m i * m j / (deg m i * deg m j) * (wt m i * wt m j) = (m i * m j) ^ 2 := by
      simp only [wt]; field_simp
    rw [hkey, Real.sqrt_sq (by nlinarith)]
  · simp [Q, h]

/-- Sum of the adjacency-indicator against any function: `∑ j, [i ~ j] f j = f (i-1) + f (i+1)`. -/
