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

lemma abs_dot_mulVec_le (A : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ nrm1 A * (v ⬝ᵥ v) := by
  rw [dot_mulVec, nrm1, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  have hij : |v i| * |v j| ≤ v ⬝ᵥ v := by
    have h1 := sq_le_dot_self v i
    have h2 := sq_le_dot_self v j
    nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
  calc |A i j * v i * v j| = |A i j| * (|v i| * |v j|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |A i j| * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_left hij (abs_nonneg _)

/-- **Weyl upper bound.**  If `B` fixes a nonzero vector orthogonal to the Perron vector of
`Q m`, then the gap is at most the entrywise distance from `Q m` to `B`. -/
