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

theorem c5_poincare_centered {y : Fin 5 → ℝ} (hy : (∑ i, y i) = 0) :
    2 * g5 * (∑ i, (y i) ^ 2) ≤ ∑ i, (y i - y (i + 1)) ^ 2 := by
  have := c5_poincare y
  rw [hy] at this
  simpa using this

end Brockian.UnbalancedPentagon

import Brockian.LimitA
import Brockian.LimitB
import Brockian.Perturb
import Brockian.LtOne
import Brockian.LowerBound

/-!
# The two extremal limits of the spectral gap

* `gap_tendsto_zero`: `gap (a t) → 0`, because `Q (a t) → Qmin` and `Qmin` has a
  two-dimensional eigenspace for its top eigenvalue `1`, so some direction orthogonal to the
  Perron vector of `a t` is almost fixed by `Q (a t)`.
* `gap_tendsto_one`: `gap (b t) → 1`, because `Q (b t) → Qmax`, whose quadratic form is
  `(zmax ⬝ x)² - (zmax' ⬝ x)²`, and the Perron direction of `b t` converges to `zmax`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Matrix Finset Filter Topology

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- For the family `a t` the gap is at most the entrywise distance from `Q (a t)` to `Qmin`. -/
