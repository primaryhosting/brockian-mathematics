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

theorem perron_b_approx_tendsto :
    Tendsto (fun t : ℕ => ∑ i, (zmax i - cb t * perron (bvec t) i) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℕ => ∑ i, (zmax i - cb t * perron (bvec t) i) ^ 2) atTop
      (𝓝 (∑ _i : Fin 5, (0:ℝ))) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    have h1 := (tendsto_const_nhds (x := zmax i) (f := atTop (α := ℕ))).sub
      (perron_b_entry_tendsto i)
    simpa using h1.pow 2
  simpa using h

end Brockian.UnbalancedPentagon

import Brockian.Defs

/-!
# The sharp Poincaré inequality on the unweighted 5-cycle

The second eigenvalue of the (unnormalized) Laplacian of `C₅` is `2 - 2 cos (2π/5) = (5-√5)/2`.
We prove the corresponding Poincaré inequality by an explicit sum-of-squares certificate:
if `M = L - κ·I + (κ/5)·J` with `κ = (5-√5)/2`, then `M² = √5 · M`, so that the quadratic
form of `M` equals `‖M y‖² / √5 ≥ 0`.
-/

namespace Brockian.UnbalancedPentagon

open Brockian.Fin5 Finset

/-- `g5 = (5 - √5)/4 = 1 - cos (2π/5)`, the second eigenvalue of the normalized Laplacian
of the balanced pentagon. -/
