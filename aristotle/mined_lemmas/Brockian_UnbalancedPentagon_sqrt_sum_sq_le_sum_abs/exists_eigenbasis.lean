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

theorem exists_eigenbasis (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.IsHermitian) :
    ∃ E : Fin 5 → (Fin 5 → ℝ),
      (∀ i j, E i ⬝ᵥ E j = if i = j then 1 else 0) ∧
      (∀ j, A *ᵥ E j = hA.eigenvalues₀ j • E j) ∧
      (∀ x : Fin 5 → ℝ, ∑ j, (E j ⬝ᵥ x) • E j = x) := by
  classical
  set σ : Fin (Fintype.card (Fin 5)) ≃ Fin 5 := Fintype.equivOfCardEq (Fintype.card_fin _) with hσ
  set B := hA.eigenvectorBasis.reindex σ.symm with hB
  refine ⟨fun j => ⇑(B j), ?_, ?_, ?_⟩
  · intro i j
    have h := orthonormal_iff_ite.mp B.orthonormal i j
    rw [show inner ℝ (B i) (B j) = ((B i).ofLp) ⬝ᵥ ((B j).ofLp) by
      simp [PiLp.inner_apply, dotProduct, mul_comm]] at h
    exact h
  · intro j
    have h := hA.mulVec_eigenvectorBasis (σ j)
    simpa [hB, Matrix.IsHermitian.eigenvalues, hσ] using h
  · intro x
    have h := B.sum_repr (WithLp.toLp 2 x)
    have h2 : ∀ j, B.repr (WithLp.toLp 2 x) j = (B j : Fin 5 → ℝ) ⬝ᵥ x := by
      intro j
      rw [B.repr_apply_apply]
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    simp only [h2] at h
    simpa using congrArg WithLp.ofLp h

section Basis

variable {A : Matrix (Fin 5) (Fin 5) ℝ} {E : Fin 5 → Fin 5 → ℝ} {lam : Fin 5 → ℝ}

/-- Parseval's identity in the eigenbasis. -/
