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

lemma nrm1_tendsto_zero {A : ℕ → Matrix (Fin 5) (Fin 5) ℝ} {B : Matrix (Fin 5) (Fin 5) ℝ}
    (h : ∀ i j, Tendsto (fun t => A t i j) atTop (𝓝 (B i j))) :
    Tendsto (fun t => nrm1 (A t - B)) atTop (𝓝 0) := by
  have : Tendsto (fun t => ∑ i, ∑ j, |A t i j - B i j|) atTop (𝓝 (∑ i : Fin 5, ∑ j : Fin 5, (0:ℝ))) := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    have := (h i j).sub tendsto_const_nhds (b := B i j)
    simpa using this.abs
  simpa [nrm1] using this

end Brockian.UnbalancedPentagon

import Brockian.Perturb

/-!
# The two limiting matrices

* `Qmin` has nonzero entries only on the edges `{2,3}` and `{4,0}`, both of weight `1`.
  It is the normalized adjacency matrix of a perfect matching on `{2,3}`, `{4,0}` plus an
  isolated vertex `1`; its spectrum is `1, 1, 0, -1, -1`.
* `Qmax` has nonzero entries only on the edges `{2,3}` and `{3,4}`, both of weight `1/√2`.
  It is the normalized adjacency matrix of the path `2 - 3 - 4` plus two isolated vertices;
  its spectrum is `1, 0, 0, 0, -1`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- The `t → ∞` limit of `Q (a t)`: the matching `{2,3} ∪ {4,0}`. -/
