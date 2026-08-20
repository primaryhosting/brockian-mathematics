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

theorem gap_eq_one_sub_eigenvalues₀_one (hm : ∀ i, 0 < m i) :
    gap m = 1 - (Q_isHermitian m).eigenvalues₀ 1 := by
  rw [gap]
  congr 1
  refine sec_eq_eigenvalues₀_one (Q_isHermitian m) ?_ ?_
  · intro hcon
    have := perron_pos hm 0
    rw [show perron m 0 = (0 : Fin 5 → ℝ) 0 from congrFun hcon 0] at this
    simp at this
  · rw [eigenvalues₀_zero_Q hm, one_smul]
    exact Q_mulVec_perron hm

end Brockian.UnbalancedPentagon

import Brockian.Rayleigh

/-!
# Workhorse lemmas for the spectral gap

`gap m = 1 - sec (Q m) (perron m)` where `sec` is the supremum of the Rayleigh quotient over
unit vectors orthogonal to the Perron vector.  Via the change of variables of
`Brockian.Rayleigh` this is exactly

`gap m = inf { En m y / Ms m y : Ctr m y = 0, y ≠ 0 }`,

and we provide the two inequalities in usable form.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

/-- Recover the "conductance coordinates" `y` of a vector `x`. -/
