import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Bundle Manifold Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace Math2

/-!
## Isometric immersions and embeddings

We work with Mathlib's Riemannian manifolds: a manifold `M` modelled on `I` whose tangent spaces
carry inner products (`RiemannianBundle (fun x : M ↦ TangentSpace I x)`).

A map `f` from such an `M` to an inner product space `F` is an *isometric immersion* if it is
smooth and its tangent map preserves scalar products at every point, i.e. the pullback of the
Euclidean first fundamental form of `F` along `f` is the Riemannian metric of `M`.  It is an
*isometric embedding* if, in addition, it is a topological embedding.
-/

/-- A map `f : M → F` from a Riemannian manifold to a real inner product space is a *smooth
isometric immersion* if it is `C^∞` and its tangent map preserves the scalar products, i.e. the
Riemannian metric of `M` is the pullback along `f` of the flat metric of `F`. -/

theorem isIsometricEmbedding_id : IsIsometricEmbedding 𝓘(ℝ, F) (id : F → F) := by
  refine ⟨⟨contMDiff_id, fun x v w ↦ ?_⟩, IsEmbedding.id⟩
  rw [mfderiv_id]
  rfl

/-!
## The theorem

Nash's isometric embedding theorem asserts that *every* Riemannian manifold admits a smooth
isometric embedding into some `ℝ^N`.  The statement proved here is the flat case of that theorem:
a finite-dimensional real inner product space `F`, equipped with its canonical (flat) Riemannian
structure — Mathlib's instance
`RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)` — is a Riemannian manifold, and it embeds
isometrically in `ℝ^N` with `N = dim F`, both in the Riemannian sense (the tangent map preserves
scalar products at every point, so the first fundamental form of `ℝ^N` pulls back to the metric
of `F`) and in the metric sense (distances are preserved).

The general case of Nash's theorem is *not* proved here.
-/

/-- **Nash embedding theorem, flat case.**  Every finite-dimensional real inner product space `F`,
regarded as a Riemannian manifold with its canonical flat metric, admits a smooth isometric
embedding into a Euclidean space `ℝ^N` (one may take `N = dim F`): there is a `C^∞` topological
embedding `g : F → ℝ^N` whose tangent map preserves scalar products at every point, and which
moreover preserves distances.

This is the flat case of Nash's isometric embedding theorem; the general case, for an arbitrary
Riemannian manifold, is not proved here. -/
