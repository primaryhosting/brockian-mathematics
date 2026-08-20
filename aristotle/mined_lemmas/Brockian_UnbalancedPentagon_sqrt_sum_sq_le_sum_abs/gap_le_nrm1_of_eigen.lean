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

theorem gap_le_nrm1_of_eigen (hm : ∀ i, 0 < m i) {B : Matrix (Fin 5) (Fin 5) ℝ} {v : Fin 5 → ℝ}
    (hv : perron m ⬝ᵥ v = 0) (hpos : 0 < v ⬝ᵥ v) (hB : B *ᵥ v = v) :
    gap m ≤ nrm1 (Q m - B) := by
  have h1 := le_sec_of_vec hm hv hpos
  have h2 : v ⬝ᵥ (Q m *ᵥ v) = v ⬝ᵥ v + v ⬝ᵥ ((Q m - B) *ᵥ v) := by
    rw [sub_mulVec, dotProduct_sub, hB]; ring
  have h3 := abs_le.mp (abs_dot_mulVec_le (Q m - B) v)
  have h4 : (1 - nrm1 (Q m - B)) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Q m *ᵥ v) := by
    rw [h2]; nlinarith [h3.1]
  have h5 : 1 - nrm1 (Q m - B) ≤ (v ⬝ᵥ (Q m *ᵥ v)) / (v ⬝ᵥ v) := (le_div_iff₀ hpos).mpr h4
  rw [gap]; linarith

/-- **Weyl lower bound.**  If the quadratic form of `B` splits as `(z ⬝ x)² - (z' ⬝ x)²` and the
Perron direction of `Q m` is `ℓ²`-close to `z` (after scaling by `c`), then `gap m` is close
to `1`. -/
