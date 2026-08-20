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

theorem Q_mulVec_perron (hm : ∀ i, 0 < m i) : Q m *ᵥ perron m = perron m := by
  funext i
  have hpi := perron_pos hm i
  have key : ∀ j, Q m i j * perron m j = (if Adj i j then m i * m j else 0) / perron m i := by
    intro j
    rw [eq_div_iff hpi.ne']
    have := Qp_mul hm i j
    linarith [this, (by ring : Q m i j * perron m j * perron m i
      = Q m i j * (perron m i * perron m j))]
  simp only [mulVec, dotProduct, key]
  rw [← Finset.sum_div]
  have : ∑ j, (if Adj i j then m i * m j else 0) = m i * deg m i := by
    have := sum_adj (fun j => m i * m j) i
    simpa [deg, mul_add] using this
  rw [this]
  rw [eq_comm, eq_div_iff hpi.ne']
  have : perron m i * perron m i = wt m i := perron_sq hm i
  rw [this]; rfl

/-! ### Change of variables -/

