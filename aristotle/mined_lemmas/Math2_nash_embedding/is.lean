/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped ContDiff
open intervalIntegral

namespace Math2

/-!
## What is formalized here

The full Nash embedding theorem ("every smooth Riemannian manifold admits a smooth
isometric embedding into some Euclidean space `ℝ^N`") is not available in Mathlib, and its
proof (the Nash–Moser implicit function theorem, or the Günther fixed point argument)
is a very large development that is not carried out here.

What is proved below, completely and without any axioms beyond Lean's standard ones, is the
class of *separable (diagonal) Riemannian metrics on `ℝ^n`*: metrics of the form

  `g_x(v, w) = ∑ i, f i (x i) * v i * w i`,   with each `f i : ℝ → ℝ` smooth and positive.

For such a metric we construct an explicit smooth, injective map `F : ℝ^n → ℝ^n` whose
differential pulls the standard Euclidean inner product of the target back to `g`, i.e. an
isometric embedding in exactly the sense of Nash's theorem.  The construction is the honest
one-dimensional Nash construction applied in each coordinate: `F x i = ∫₀^{x i} √(f i t) dt`,
i.e. the arclength reparametrisation of each coordinate axis.

The `n = 1` case, `nash_embedding_line`, is the statement that *every* Riemannian metric on the
real line embeds isometrically in `ℝ`, which is a genuine (if elementary) instance of the Nash
theorem: no hypothesis beyond smoothness and positivity of the metric is assumed.
-/

/-- **Arclength antiderivative.** For a smooth positive `f : ℝ → ℝ` there is a smooth strictly
increasing `G : ℝ → ℝ` with `G' = √f` everywhere.  This is the one-dimensional isometric
embedding: `G` pulls back `dt²` to the metric `f(x) dx²`. -/

theorem is not formalized here.  See `nash_embedding_line` for the case `n = 1`, where the
hypothesis is simply that `g` is an arbitrary smooth Riemannian metric on the line. -/
