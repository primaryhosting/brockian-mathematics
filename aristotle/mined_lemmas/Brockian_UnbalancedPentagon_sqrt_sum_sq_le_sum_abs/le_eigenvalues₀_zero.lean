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

theorem le_eigenvalues₀_zero {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsHermitian)
    {v : Fin 5 → ℝ} {mu : ℝ} (hv : v ≠ 0) (hvA : A *ᵥ v = mu • v) :
    mu ≤ hA.eigenvalues₀ 0 := by
  obtain ⟨E, horth, heig, hcomp⟩ := exists_eigenbasis A hA
  have hsymm := transpose_eq_of_isHermitian hA
  by_contra hcon
  push_neg at hcon
  have hall : ∀ j, E j ⬝ᵥ v = 0 := by
    intro j
    have h := eigen_coeff_eq_zero hsymm heig hvA j
    rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      have hle : hA.eigenvalues₀ j ≤ hA.eigenvalues₀ 0 := hA.eigenvalues₀_antitone (Fin.zero_le j)
      linarith
    · exact h'
  have := dot_self_eq_sum_coeff_sq hcomp v
  rw [Finset.sum_congr rfl (fun j _ => by rw [hall j]; ring : ∀ j ∈ Finset.univ,
    (E j ⬝ᵥ v) ^ 2 = (0:ℝ))] at this
  simp only [Finset.sum_const, smul_zero] at this
  exact absurd this (dot_self_pos hv).ne'

/-- A uniform bound on the Rayleigh form bounds the top ordered eigenvalue. -/
