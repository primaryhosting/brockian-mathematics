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

theorem gap_avec_le (t : ℕ) (ht : 1 ≤ t) : gap (avec t) ≤ nrm1 (Q (avec t) - Qmin) := by
  have hpos := avec_pos ht
  have p0 := perron_pos hpos 0
  have p2 := perron_pos hpos 2
  have p3 := perron_pos hpos 3
  have p4 := perron_pos hpos 4
  set α : ℝ := perron (avec t) 0 + perron (avec t) 4 with hα
  set β : ℝ := -(perron (avec t) 2 + perron (avec t) 3) with hβ
  have hαpos : 0 < α := by rw [hα]; linarith
  refine gap_le_nrm1_of_eigen hpos (v := ![β, 0, α, α, β]) ?_ ?_ (Qmin_mulVec_top α β)
  · have e0 : (![β, 0, α, α, β] : Fin 5 → ℝ) 0 = β := rfl
    have e1 : (![β, 0, α, α, β] : Fin 5 → ℝ) 1 = 0 := rfl
    have e2 : (![β, 0, α, α, β] : Fin 5 → ℝ) 2 = α := rfl
    have e3 : (![β, 0, α, α, β] : Fin 5 → ℝ) 3 = α := rfl
    have e4 : (![β, 0, α, α, β] : Fin 5 → ℝ) 4 = β := rfl
    simp only [dotProduct, Fin.sum_univ_five, e0, e1, e2, e3, e4]
    rw [hα, hβ]; ring
  · have e0 : (![β, 0, α, α, β] : Fin 5 → ℝ) 0 = β := rfl
    have e1 : (![β, 0, α, α, β] : Fin 5 → ℝ) 1 = 0 := rfl
    have e2 : (![β, 0, α, α, β] : Fin 5 → ℝ) 2 = α := rfl
    have e3 : (![β, 0, α, α, β] : Fin 5 → ℝ) 3 = α := rfl
    have e4 : (![β, 0, α, α, β] : Fin 5 → ℝ) 4 = β := rfl
    simp only [dotProduct, Fin.sum_univ_five, e0, e1, e2, e3, e4]
    nlinarith [sq_nonneg β, hαpos]

/-- **Target 3.** `gap (a t) → 0` as `t → ∞`. -/
