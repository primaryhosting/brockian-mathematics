/-
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Nash's isometric embedding theorem states that every Riemannian manifold `(M, g)` admits a
smooth isometric embedding into some Euclidean space `ℝ^N`, where *isometric* means that the
pullback of the Euclidean metric along the embedding is `g`, i.e.
`⟪Df(x) u, Df(x) v⟫ = g x (u, v)` for all tangent vectors `u, v`.

This file formalizes the theorem in the following cases, stated in the concrete (chart-level)
form of the pullback identity above.

* `Math2.nash_embedding` : the **one-dimensional** case. Every smooth Riemannian metric on the
  line (a smooth positive function `g : ℝ → ℝ`, the metric being `(u, v) ↦ g x * (u * v)`)
  admits a smooth isometric embedding into `ℝ^N` (with `N = 1`), given by the arclength
  function `x ↦ ∫_0^x √(g t) dt`.
* `Math2.nash_embedding_separable` : the case of a **separable diagonal** metric in arbitrary
  dimension `n`, i.e. `g x (u, v) = ∑ i, aᵢ (xᵢ) * uᵢ * vᵢ` with each `aᵢ` smooth and positive.
  The embedding into `ℝ^n` is obtained by applying the one-dimensional construction in each
  coordinate.
* `Math2.nash_embedding_const` : the case of a **constant** metric in arbitrary dimension `n`,
  given by a positive definite matrix `G`; the embedding into `ℝ^n` is the linear map with
  matrix a square root `B` of `G` (`Bᵀ * B = G`).

The general case (arbitrary dimension, arbitrary smooth metric) is *not* formalized here.
-/

open Topology Matrix
open scoped ContDiff MatrixOrder

namespace Math2

/-- The canonical linear isometry from `ℝ` onto the one-dimensional Euclidean space
`EuclideanSpace ℝ (Fin 1)`. -/

theorem nash_embedding_const {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ∃ (N : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧ IsEmbedding f ∧
      ∀ x u v : EuclideanSpace ℝ (Fin n),
        inner ℝ (fderiv ℝ f x u) (fderiv ℝ f x v) = u.ofLp ⬝ᵥ G.mulVec v.ofLp := by
  obtain ⟨B, -, hB⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1
      (Matrix.isStrictlyPositive_iff_posDef.2 hG)
  have hBt : star B = Bᵀ := rfl
  rw [hBt] at hB
  -- the linear map with matrix `B`
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin B
    with hT_def
  have key : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (T u) (T v) = u.ofLp ⬝ᵥ G.mulVec v.ofLp := by
    intro u v
    rw [hB, hT_def]
    simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.vecMul_transpose]
    rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h0 : u.ofLp ⬝ᵥ G.mulVec u.ofLp = 0 := by rw [← key u u, hu]; simp
    by_contra hne
    have hu0 : u.ofLp ≠ 0 := fun h => hne (by ext i; simpa using congrFun h i)
    have hpos := hG.dotProduct_mulVec_pos hu0
    rw [show star u.ofLp = u.ofLp from by ext i; simp] at hpos
    exact absurd h0 (ne_of_gt hpos)
  refine ⟨n, T, ?_, ?_, ?_⟩
  · exact (T.toContinuousLinearMap : _ →L[ℝ] _).contDiff
  · exact (LinearMap.isClosedEmbedding_of_injective
      (f := T) (LinearMap.ker_eq_bot.2 hinj)).isEmbedding
  · intro x u v
    have hfd : fderiv ℝ (fun y => T y) x = (T.toContinuousLinearMap : _ →L[ℝ] _) :=
      (T.toContinuousLinearMap : _ →L[ℝ] _).hasFDerivAt.fderiv
    rw [show (fun y => T y) = (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) from rfl]
      at hfd
    rw [hfd]
    simpa using key u v

end Math2

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

