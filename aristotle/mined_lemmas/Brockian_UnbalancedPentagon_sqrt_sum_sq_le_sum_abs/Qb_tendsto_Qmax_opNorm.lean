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

theorem Qb_tendsto_Qmax_opNorm :
    Tendsto (fun t : ℕ => ‖Q (bvec t) - Qmax‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => opNorm_le_nrm1 _) Qb_tendsto_Qmax

end Brockian.UnbalancedPentagon

import Brockian.LimitMatrices

/-!
# The two extremal families of fibre sizes

* `aN t = (t², 1, t², t, t)` drives the gap to `0`;
* `bN t = (1, 1, t, t², t)` drives the gap to `1`.

This file records their entrywise data and the elementary limit machinery: every quantity we
must control is `√(rational function of 1/t)`, so it is the value at `u = 0` of a function
continuous at `0`, evaluated at `u = 1/t`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- The "gap → 0" family of fibre sizes. -/
