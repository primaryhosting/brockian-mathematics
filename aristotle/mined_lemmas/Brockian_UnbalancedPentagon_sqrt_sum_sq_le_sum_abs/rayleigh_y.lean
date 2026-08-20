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

lemma rayleigh_y (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ) :
    (fun i => perron m i * y i) ⬝ᵥ (Q m *ᵥ (fun i => perron m i * y i)) = Ms m y - En m y := by
  rw [dot_mulVec]
  rw [← energy_identity m y]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := Qp_mul hm i j
  calc Q m i j * (perron m i * y i) * (perron m j * y j)
      = (Q m i j * (perron m i * perron m j)) * (y i * y j) := by ring
    _ = _ := by rw [this]

end Brockian.UnbalancedPentagon

import Brockian.FamilyDefs

/-!
# Entrywise limits for the family `b t = (1, 1, t, t², t)`

With `d = (t+1, 1+t, 1+t², 2t, t²+1)` the nonzero entries of `Q (b t)` are, for `t ≥ 1`,

* `Q (b t) 0 1 = 1/(t+1)`,
* `Q (b t) 1 2 = √(t/((1+t)(1+t²)))`,
* `Q (b t) 2 3 = √(t²/(2(1+t²)))`,
* `Q (b t) 3 4 = √(t²/(2(1+t²)))`,
* `Q (b t) 4 0 = √(t/((1+t²)(1+t)))`,

together with the symmetric ones; so `Q (b t) → Qmax` entrywise.

The Perron vector is `p i = √(D i)` with `D = (t+1, 1+t, t+t³, 2t³, t³+t)`; rescaled by
`cb t = 1/√(4t³)` it converges to `zmax = (0, 0, 1/2, √2/2, 1/2)`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

