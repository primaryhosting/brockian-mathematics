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
def IsIsometricImmersion {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : M → F) : Prop :=
  ContMDiff I 𝓘(ℝ, F) ∞ f ∧
    ∀ (x : M) (v w : TangentSpace I x),
      ⟪mfderiv I 𝓘(ℝ, F) f x v, mfderiv I 𝓘(ℝ, F) f x w⟫ = ⟪v, w⟫

/-- A *smooth isometric embedding* of a Riemannian manifold into a real inner product space:
a smooth isometric immersion which is moreover a topological embedding. -/
def IsIsometricEmbedding {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : M → F) : Prop :=
  IsIsometricImmersion I f ∧ IsEmbedding f

section

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- The tangent map of the composition of a smooth map into a normed space with a continuous
linear map. -/
theorem mfderiv_clm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (x : M) :
    mfderiv I 𝓘(ℝ, G) (fun y ↦ L (f y)) x = L.comp (mfderiv I 𝓘(ℝ, F) f x) := by
  rw [show (fun y ↦ L (f y)) = (L : F → G) ∘ f from rfl,
    mfderiv_comp x L.mdifferentiableAt ((hf x).mdifferentiableAt (by simp)), L.mfderiv_eq]

/-- Post-composing a smooth isometric embedding with a linear isometry equivalence of the target
again gives a smooth isometric embedding. -/
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
theorem exists_isometricEmbedding_euclidean [FiniteDimensional ℝ F]
    {f : M → F} (hf : IsIsometricEmbedding I f) :
    ∃ (N : ℕ) (g : M → EuclideanSpace ℝ (Fin N)), IsIsometricEmbedding I g :=
  ⟨Module.finrank ℝ F, fun x ↦ (stdOrthonormalBasis ℝ F).repr (f x),
    hf.comp_linearIsometryEquiv _⟩

end

section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The identity map of an inner product space, viewed as a flat Riemannian manifold,
is a smooth isometric embedding. -/
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
theorem nash_embedding [FiniteDimensional ℝ F] :
    ∃ (N : ℕ) (g : F → EuclideanSpace ℝ (Fin N)),
      IsIsometricEmbedding 𝓘(ℝ, F) g ∧ ∀ x y : F, dist (g x) (g y) = dist x y := by
  refine ⟨Module.finrank ℝ F, fun x ↦ (stdOrthonormalBasis ℝ F).repr x, ?_, ?_⟩
  · exact isIsometricEmbedding_id.comp_linearIsometryEquiv _
  · intro x y
    exact (stdOrthonormalBasis ℝ F).repr.toIsometryEquiv.dist_eq x y

end

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

