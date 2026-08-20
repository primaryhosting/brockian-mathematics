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

lemma nonempty_rayleighSet (hm : ∀ i, 0 < m i) :
    (rayleighSet (Q m) (perron m)).Nonempty := by
  have h0 := wt_pos hm 0
  have h1 := wt_pos hm 1
  set y : Fin 5 → ℝ := ![wt m 1, -(wt m 0), 0, 0, 0] with hy
  have hCtr : Ctr m y = 0 := by rw [Ctr_eq]; simp [hy]; ring
  have hMs : 0 < Ms m y := by
    rw [Ms_eq]; simp only [hy]; norm_num
    have h2 := wt_pos hm 2
    have h3 := wt_pos hm 3
    have h4 := wt_pos hm 4
    positivity
  refine ⟨_, mem_rayleighSet_of_vec (w := fun i => perron m i * y i) ?_ ?_⟩
  · rw [dot_perron_y hm y]; exact hCtr
  · rw [dot_self_y hm y]; exact hMs

