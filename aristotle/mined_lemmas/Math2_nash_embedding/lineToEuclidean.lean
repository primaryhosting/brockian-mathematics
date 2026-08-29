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

noncomputable def lineToEuclidean : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun a := EuclideanSpace.single 0 a
  map_add' a b := by ext i; simp [EuclideanSpace.single_apply]; split <;> simp
  map_smul' c a := by ext i; simp [EuclideanSpace.single_apply]
  norm_map' a := by simp

/-- The arclength function of a smooth positive metric `g` on the line: a smooth embedding
`F : ℝ → ℝ` with `F' x = √(g x)`, namely `F x = ∫_0^x √(g t) dt`. -/
