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

theorem IsIsometricEmbedding.comp_linearIsometryEquiv
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (L : F ≃ₗᵢ[ℝ] G) {f : M → F} (hf : IsIsometricEmbedding I f) :
    IsIsometricEmbedding I (fun x ↦ L (f x)) := by
  obtain ⟨⟨hsmooth, hinner⟩, hemb⟩ := hf
  refine ⟨⟨L.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp hsmooth, ?_⟩,
    L.toHomeomorph.isEmbedding.comp hemb⟩
  intro x v w
  have hfun : (fun y ↦ L (f y)) =
      fun y ↦ L.toContinuousLinearEquiv.toContinuousLinearMap (f y) := rfl
  rw [hfun, mfderiv_clm_comp L.toContinuousLinearEquiv.toContinuousLinearMap hsmooth x]
  show ⟪L (mfderiv I 𝓘(ℝ, F) f x v), L (mfderiv I 𝓘(ℝ, F) f x w)⟫ = ⟪v, w⟫
  rw [L.inner_map_map]
  exact hinner x v w

/-- **Reduction of isometric embeddings to Euclidean space.**  If a Riemannian manifold `M` admits
a smooth isometric embedding into some finite-dimensional real inner product space, then it admits
a smooth isometric embedding into a standard Euclidean space `ℝ^N`. -/
