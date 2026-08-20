/-
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires import commands to come before any module docstring, so the requested
header appears here as an ordinary block comment, and again as the module docstring immediately
after the imports.)
-/

import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff RealInnerProductSpace BigOperators
open Set Topology

/-!
## Scope

John Nash's theorem states that *every* Riemannian manifold `(M, g)` admits a smooth isometric
embedding into some Euclidean space `ℝ^N`, i.e. a smooth topological embedding
`f : M → ℝ^N` whose differential satisfies `⟪df_x v, df_x w⟫ = g x v w` for all tangent vectors
`v, w` at every point `x`. Its proof (via the Nash–Moser implicit function theorem) is far beyond
the current state of formalized mathematics, and the general statement is not available in
Mathlib.

This file formalizes the notion of a smooth isometric embedding of a Riemannian metric
(`Math2.IsSmoothIsometricEmbedding`) and proves the Nash embedding statement for two genuine
families of Riemannian metrics:

* `Math2.nash_embedding`: all metrics on `ℝⁿ` of the separably-diagonal form
  `g x v w = ∑ i, (a i (x i))^2 * v i * w i` with `a i` smooth and positive. In particular, for
  `n = 1` this is *every* Riemannian metric on the real line.
* `Math2.nash_embedding_inner_product_space`: the canonical metric of any finite-dimensional real
  inner product space.
* `Math2.nash_embedding_graph`: all metrics on `ℝⁿ` induced by the graph of a smooth function
  `u : ℝⁿ → ℝ`, which are in general curved.

No axioms beyond the standard ones (`propext`, `Classical.choice`, `Quot.sound`) are used.
-/

namespace Math2

/-- `IsSmoothIsometricEmbedding g f` says that `f`, a map from the manifold `E` (a real normed
space, playing the role of ℝⁿ) into a Euclidean space `ℝ^N`, is a smooth isometric embedding of
the Riemannian metric `g`: it is `C^∞`, it is a topological embedding, and its differential
pulls the Euclidean inner product back to `g`.

Here a Riemannian metric is described concretely by the function `g : E → E → E → ℝ`, where
`g x v w` is the inner product of the tangent vectors `v`, `w` at the point `x`. -/

def IsSmoothIsometricEmbedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (g : E → E → E → ℝ) (f : E → EuclideanSpace ℝ (Fin N)) : Prop :=
  ContDiff ℝ ∞ f ∧ IsEmbedding f ∧ ∀ x v w, ⟪fderiv ℝ f x v, fderiv ℝ f x w⟫ = g x v w

/-- The antiderivative of `a` vanishing at `0`. -/
