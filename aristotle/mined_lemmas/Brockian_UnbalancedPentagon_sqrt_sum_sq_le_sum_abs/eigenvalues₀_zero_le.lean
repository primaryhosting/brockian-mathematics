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

theorem eigenvalues₀_zero_le {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ x : Fin 5 → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)) : hA.eigenvalues₀ 0 ≤ c := by
  obtain ⟨E, horth, heig, hcomp⟩ := exists_eigenbasis A hA
  have h0 : (E 0) ⬝ᵥ (A *ᵥ E 0) = hA.eigenvalues₀ 0 := by
    rw [heig 0, dotProduct_smul, smul_eq_mul, horth 0 0, if_pos rfl, mul_one]
  have h1 : (E 0) ⬝ᵥ (E 0) = 1 := by rw [horth 0 0, if_pos rfl]
  have := h (E 0)
  rw [h0, h1, mul_one] at this
  exact this

/-! ### The main bridge theorem -/

/-- **The Rayleigh definition of `sec` computes the second largest eigenvalue.**
If `v` is a nonzero eigenvector of the real symmetric matrix `A` for its largest eigenvalue,
then the supremum of the Rayleigh quotient over unit vectors orthogonal to `v` is the second
largest eigenvalue of `A`. -/
