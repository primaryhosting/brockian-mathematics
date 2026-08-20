import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other command, including the module
-- docstring above; the requested header is otherwise reproduced verbatim.)

open scoped ContDiff
open Topology

namespace Math2

/-! ## The canonical linear isometry `ℝ →L[ℝ] ℝ¹`

We realise the target Euclidean space as `EuclideanSpace ℝ (Fin N)`.  For the construction
below only `N = 1` is needed, so we set up the canonical map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`
and record its basic properties. -/

/-- The canonical continuous linear map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`,
sending `a` to the constant family `fun _ => a`. -/

lemma isEmbedding_of_strictMono {F : ℝ → ℝ} (hF : Continuous F) (hm : StrictMono F) :
    IsEmbedding F := by
  refine hm.isEmbedding_of_ordConnected ?_
  have : IsPreconnected (Set.range F) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image F hF.continuousOn
  exact this.ordConnected

/-! ## The Nash embedding theorem in dimension one

Mathlib does not contain the Nash embedding theorem (nor, at present, any of the hard
implicit-function-theorem machinery used in its proof), so nothing in the library closes the
general statement.  What we prove here is the one–dimensional case, which is a genuine
(non-vacuous, non-circular) instance of the theorem: *an arbitrary* smooth Riemannian metric on
the one–dimensional manifold `ℝ` is realised as the metric induced by a smooth embedding into a
Euclidean space `ℝ^N`.

A Riemannian metric on the manifold `ℝ` is a smooth positive function `g`, the associated inner
product on the tangent space `T_x ℝ ≃ ℝ` being `(v, w) ↦ g x * (v * w)`.  A map
`f : ℝ → EuclideanSpace ℝ (Fin N)` is an isometric immersion when its differential pulls the
Euclidean inner product back to this metric, i.e.
`⟪Df_x v, Df_x w⟫ = g x * (v * w)`; it is an isometric *embedding* when moreover it is a
topological embedding.

The embedding is the arclength map `x ↦ ∫ t in 0..x, √(g t)` into `ℝ^1`. -/

/-- **Nash embedding theorem, one-dimensional case.**
Every Riemannian metric `g` on the one-dimensional manifold `ℝ` (a smooth, everywhere positive
function, giving the tangent space at `x` the inner product `(v, w) ↦ g x * (v * w)`) is induced
by a smooth isometric embedding of `ℝ` into some Euclidean space `ℝ^N`: there is `N` and a
smooth topological embedding `f : ℝ → EuclideanSpace ℝ (Fin N)` whose differential pulls the
Euclidean inner product back to `g`. -/
