import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma schrodinger_isSymmetric (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) :
    IsSymmetricOp (schrodingerOp b V) := by
  -- first: symmetry when the left argument is a basis vector
  have step2 : ∀ (m : ℤ) (y : schrodingerDomain b),
      ⟪schrodingerOp b V (domBasis b m), (y : E)⟫_ℂ
        = ⟪(b m : E), schrodingerOp b V y⟫_ℂ := by
    intro m
    have hfg : ((innerSL ℂ (schrodingerOp b V (domBasis b m))).toLinearMap ∘ₗ
          (schrodingerDomain b).subtype : schrodingerDomain b →ₗ[ℂ] ℂ) =
        ((innerSL ℂ (b m)).toLinearMap ∘ₗ schrodingerOp b V :
          schrodingerDomain b →ₗ[ℂ] ℂ) := by
      refine (domBasis b).ext fun n => ?_
      simpa using schrodinger_symm_basis b V m n
    intro y
    simpa using LinearMap.congr_fun hfg y
  intro x y
  have hfg : ((innerSL ℂ ((y : E))).toLinearMap ∘ₗ schrodingerOp b V :
        schrodingerDomain b →ₗ[ℂ] ℂ) =
      ((innerSL ℂ (schrodingerOp b V y)).toLinearMap ∘ₗ (schrodingerDomain b).subtype :
        schrodingerDomain b →ₗ[ℂ] ℂ) := by
    refine (domBasis b).ext fun m => ?_
    have h := step2 m y
    have h' : ⟪(y : E), schrodingerOp b V (domBasis b m)⟫_ℂ = ⟪schrodingerOp b V y, (b m : E)⟫_ℂ := by
      rw [← inner_conj_symm ((y : E)), h, inner_conj_symm]
    simpa using h'
  have h2 : ⟪(y : E), schrodingerOp b V x⟫_ℂ = ⟪schrodingerOp b V y, (x : E)⟫_ℂ := by
    simpa using LinearMap.congr_fun hfg x
  rw [← inner_conj_symm (schrodingerOp b V x), h2, inner_conj_symm]

/-- Square-summability of the coefficients of a vector in a Hilbert basis. -/
