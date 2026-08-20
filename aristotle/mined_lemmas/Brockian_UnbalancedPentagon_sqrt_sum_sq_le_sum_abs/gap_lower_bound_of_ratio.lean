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

theorem gap_lower_bound_of_ratio (hm : ∀ i, 0 < m i) : g5 / (rho m) ^ 2 ≤ gap m := by
  have hmin := mmin_pos hm
  have hmax := mmax_pos hm
  have hrw : g5 / (rho m) ^ 2 = g5 * (mmin m) ^ 2 / (mmax m) ^ 2 := by
    rw [rho, div_pow, div_div_eq_mul_div]
  rw [hrw]
  exact le_gap_of_poincare hm fun y hC => weighted_poincare hm y hC

end Brockian.UnbalancedPentagon

import Brockian.FamilyDefs

/-!
# Entrywise limits for the family `a t = (t², 1, t², t, t)`

With `d = (t+1, 2t², 1+t, t²+t, t+t²)` the nonzero entries of `Q (a t)` are, for `t ≥ 1`,

* `Q (a t) 0 1 = Q (a t) 1 0 = √(1/(2(t+1)))`,
* `Q (a t) 1 2 = Q (a t) 2 1 = √(1/(2(t+1)))`,
* `Q (a t) 2 3 = Q (a t) 3 2 = t/(t+1)`,
* `Q (a t) 3 4 = Q (a t) 4 3 = 1/(t+1)`,
* `Q (a t) 4 0 = Q (a t) 0 4 = t/(t+1)`,

so `Q (a t) → Qmin` entrywise, with error `O(1/√t)`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

section Entries

variable {t : ℕ}

