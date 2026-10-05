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
