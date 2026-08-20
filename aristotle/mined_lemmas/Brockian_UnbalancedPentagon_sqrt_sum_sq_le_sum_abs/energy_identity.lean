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

lemma energy_identity (m y : Fin 5 → ℝ) :
    ∑ i, ∑ j, (if Adj i j then m i * m j else 0) * (y i * y j) = Ms m y - En m y := by
  have h : ∀ i : Fin 5, ∑ j, (if Adj i j then m i * m j else 0) * (y i * y j)
      = ∑ j, (if Adj i j then (fun j => m i * m j * (y i * y j)) j else 0) := by
    intro i
    exact Finset.sum_congr rfl fun j _ => by by_cases h : Adj i j <;> simp [h]
  simp only [h, sum_adj]
  rw [En_eq, Ms_eq, Fin.sum_univ_five]
  simp only [wt, deg_zero, deg_one, deg_two, deg_three, deg_four]
  simp only [Fin5.add_one_0, Fin5.add_one_1, Fin5.add_one_2, Fin5.add_one_3, Fin5.add_one_4,
    Fin5.sub_one_0, Fin5.sub_one_1, Fin5.sub_one_2, Fin5.sub_one_3, Fin5.sub_one_4]
  ring

