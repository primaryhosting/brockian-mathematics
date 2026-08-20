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

lemma mem_rayleighSet_of_vec {A : Matrix (Fin 5) (Fin 5) ℝ} {v w : Fin 5 → ℝ}
    (hw : v ⬝ᵥ w = 0) (hpos : 0 < w ⬝ᵥ w) :
    (w ⬝ᵥ (A *ᵥ w)) / (w ⬝ᵥ w) ∈ rayleighSet A v := by
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s * s = w ⬝ᵥ w :=
    ⟨Real.sqrt (w ⬝ᵥ w), Real.sqrt_pos.mpr hpos, Real.mul_self_sqrt hpos.le⟩
  have hcc : s⁻¹ * s⁻¹ * (w ⬝ᵥ w) = 1 := by rw [← hs2]; field_simp
  refine ⟨s⁻¹ • w, ?_, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]; exact hcc
  · rw [dotProduct_smul, smul_eq_mul, hw, mul_zero]
  · rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      div_eq_iff hpos.ne']
    linear_combination (-(w ⬝ᵥ (A *ᵥ w))) * hcc

/-- Any vector orthogonal to the Perron vector gives a lower bound on `sec`. -/
