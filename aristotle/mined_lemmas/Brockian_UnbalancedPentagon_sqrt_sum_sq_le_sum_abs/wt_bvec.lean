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

lemma wt_bvec (t : ℕ) :
    wt (bvec t) 0 = (t : ℝ) + 1 ∧ wt (bvec t) 1 = 1 + (t : ℝ) ∧
    wt (bvec t) 2 = (t : ℝ) * (1 + (t : ℝ) ^ 2) ∧ wt (bvec t) 3 = 2 * (t : ℝ) ^ 3 ∧
    wt (bvec t) 4 = (t : ℝ) * ((t : ℝ) ^ 2 + 1) := by
  obtain ⟨d0, d1, d2, d3, d4⟩ := deg_bvec t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [wt, d0, d1, d2, d3, d4]; simp; try ring)

