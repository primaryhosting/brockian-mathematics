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

theorem gap_tendsto_one : Tendsto (fun t : ℕ => gap (bvec t)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun t : ℕ =>
      1 - (∑ i, (zmax i - cb t * perron (bvec t) i) ^ 2) - nrm1 (Q (bvec t) - Qmax))
      atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub
      perron_b_approx_tendsto).sub Qb_tendsto_Qmax
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with t ht using le_gap_bvec t ht
  · filter_upwards [eventually_ge_atTop 1] with t ht using (gap_lt_one (bvec_pos ht)).le

end Brockian.UnbalancedPentagon

import Brockian.Gap

/-!
# Elementary Weyl-type perturbation bounds for real symmetric `5 × 5` matrices

All the eigenvalue continuity we need is packaged in two statements.

* `gap_le_nrm1_of_eigen`: if `B` fixes a vector `v` orthogonal to the Perron vector of `m`,
  then `gap m ≤ ‖Q m - B‖₁` (entrywise `ℓ¹` norm).  This is a Weyl upper bound for the gap.
* `le_gap_of_approx`: if the quadratic form of `B` is dominated by `(z ⬝ x)²` and the Perron
  direction of `m` is close to `z`, then `gap m` is close to `1`.

The entrywise `ℓ¹` norm `nrm1` dominates the `ℓ²` operator norm (see `Brockian.OpNorm`).
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

