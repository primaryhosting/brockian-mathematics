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

theorem isEmbedding_iota : Topology.IsEmbedding (iota : ℝ → EuclideanSpace ℝ (Fin 1)) :=
  (AddMonoidHomClass.isometry_of_norm iota norm_iota).isEmbedding

/-- **Nash embedding on the line.** Every smooth Riemannian metric on `ℝ` admits a smooth
isometric embedding into `ℝ¹`, namely the arc-length parametrisation. -/
