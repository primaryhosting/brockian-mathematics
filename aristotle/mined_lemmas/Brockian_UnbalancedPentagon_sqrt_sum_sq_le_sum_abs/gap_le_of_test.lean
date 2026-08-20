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

theorem gap_le_of_test (hm : ∀ i, 0 < m i) (y : Fin 5 → ℝ)
    (hC : Ctr m y = 0) (hM : 0 < Ms m y) : gap m ≤ En m y / Ms m y := by
  have hww : (fun i => perron m i * y i) ⬝ᵥ (fun i => perron m i * y i) = Ms m y :=
    dot_self_y hm y
  have h1 : perron m ⬝ᵥ (fun i => perron m i * y i) = 0 := by rw [dot_perron_y hm y]; exact hC
  have h2 : 0 < (fun i => perron m i * y i) ⬝ᵥ (fun i => perron m i * y i) := by
    rw [hww]; exact hM
  have h4 := le_sec_of_vec hm h1 h2
  rw [rayleigh_y hm y, hww] at h4
  have h5 : (Ms m y - En m y) / Ms m y = 1 - En m y / Ms m y := by field_simp
  rw [h5] at h4
  rw [gap]; linarith

/-- Lower bound for the gap from a weighted Poincaré inequality. -/
