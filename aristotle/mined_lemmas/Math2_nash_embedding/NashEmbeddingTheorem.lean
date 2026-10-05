import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff
open Bundle

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Math2

/-!
## Isometric embeddings of Riemannian manifolds into Euclidean space

Throughout, a *Riemannian manifold* is a smooth manifold `M` modelled on `(E, H, I)` whose
tangent bundle carries a `RiemannianBundle` structure, i.e. each tangent space
`TangentSpace I x` is endowed with an inner product (varying smoothly with `x` when one also
assumes `IsContMDiffRiemannianBundle`).  This is the Mathlib formulation of a Riemannian metric.
-/

/-- A map `f : M → ℝ^N` is an **isometric embedding** of the Riemannian manifold `M` if it is
smooth, a topological embedding, and its differential preserves inner products, i.e. the pullback
along `f` of the Euclidean metric of `ℝ^N` is the Riemannian metric of `M`. -/

def NashEmbeddingTheorem : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)],
    ∃ (N : ℕ) (f : M → EuclideanSpace ℝ (Fin N)), IsIsometricEmbedding I M N f

/-!
## The flat case: an arbitrary constant Riemannian metric

A finite dimensional real inner product space `F`, equipped with its canonical Riemannian metric
(the given inner product on every tangent space), embeds isometrically into
`ℝ^(finrank ℝ F)`.  Since `F` may carry *any* inner product, this is exactly the statement that an
arbitrary constant Riemannian metric on `ℝ^n` is realised by an embedding into Euclidean space.
-/

/-- **Nash embedding, constant metric case.**  Every finite dimensional real inner product space,
viewed as a Riemannian manifold with its canonical (constant) Riemannian metric, admits a smooth
isometric embedding into a Euclidean space `ℝ^N`. -/
