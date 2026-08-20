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

theorem gap_lt_one (hm : ∀ i, 0 < m i) : gap m < 1 := by
  have w0 := wt_pos hm 0
  have w1 := wt_pos hm 1
  have w2 := wt_pos hm 2
  have w3 := wt_pos hm 3
  have w4 := wt_pos hm 4
  set τ : ℝ := -(wt m 0 + wt m 1) / wt m 3 with hτ
  set y : Fin 5 → ℝ := ![1, 1, 0, τ, 0] with hy
  have hy0 : y 0 = 1 := rfl
  have hy1 : y 1 = 1 := rfl
  have hy2 : y 2 = 0 := rfl
  have hy3 : y 3 = τ := rfl
  have hy4 : y 4 = 0 := rfl
  have hC : Ctr m y = 0 := by
    rw [Ctr_eq, hy0, hy1, hy2, hy3, hy4, hτ]
    have h3 : wt m 3 ≠ 0 := ne_of_gt w3
    field_simp
    ring
  have hM : 0 < Ms m y := by
    rw [Ms_eq, hy0, hy1, hy2, hy3, hy4]
    have : 0 ≤ wt m 3 * τ ^ 2 := by positivity
    nlinarith
  have hE : En m y = Ms m y - 2 * (m 0 * m 1) := by
    rw [En_eq, Ms_eq, hy0, hy1, hy2, hy3, hy4]
    simp only [wt, deg_zero, deg_one, deg_two, deg_three, deg_four]
    ring
  have hle := gap_le_of_test hm y hC hM
  rw [hE] at hle
  have hlt : (Ms m y - 2 * (m 0 * m 1)) / Ms m y < 1 := by
    rw [div_lt_one hM]
    have := mul_pos (hm 0) (hm 1)
    linarith
  linarith

end Brockian.UnbalancedPentagon

import Brockian.LimitMatrices

/-!
# Ordered eigenvalues of the two limiting matrices

We compute the characteristic polynomials of `Qmin` and `Qmax` explicitly and deduce their
ordered eigenvalue lists:

* `Qmin` has spectrum `1, 1, 0, -1, -1`;
* `Qmax` has spectrum `1, 0, 0, 0, -1`.

The bridge from a factored characteristic polynomial to Mathlib's ordered eigenvalues
`Matrix.IsHermitian.eigenvalues₀` is `eigenvalues₀_eq_of_charpoly`.
-/

namespace Brockian.UnbalancedPentagon

open Matrix Polynomial

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- If the characteristic polynomial of a real symmetric `5 × 5` matrix factors with the
antitone root list `μ`, then `μ` is exactly the list of ordered eigenvalues. -/
