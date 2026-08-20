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

lemma gap_nonneg (hm : ∀ i, 0 < m i) : 0 ≤ gap m := by
  refine le_gap_of_poincare hm ?_
  intro y _
  simpa using En_nonneg (fun i => (hm i).le) y

end Brockian.UnbalancedPentagon

import Brockian.Defs

/-!
# The Rayleigh quotient of `Q m` in "conductance" coordinates

Writing a vector `x` as `x i = perron m i * y i` turns the Rayleigh quotient of `Q m`
into the classical weighted Poincaré quotient of the 5-cycle:

* `x ⬝ᵥ x = Ms m y = ∑ i, D i * (y i)^2`,
* `perron m ⬝ᵥ x = Ctr m y = ∑ i, D i * y i`,
* `x ⬝ᵥ (Q m *ᵥ x) = Ms m y - En m y` with `En m y = ∑_{edges} m i * m j * (y i - y j)^2`.

Consequently the spectral gap is
`gap m = inf { En m y : Ms m y = 1, Ctr m y = 0 }`,
and we record the two directions of that description as usable lemmas.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset

variable {m : Fin 5 → ℝ}

