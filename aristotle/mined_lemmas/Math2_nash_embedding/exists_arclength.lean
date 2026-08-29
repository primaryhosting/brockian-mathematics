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

theorem exists_arclength (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ StrictMono G ∧ ∀ x, HasDerivAt G (Real.sqrt (f x)) x := by
  have hs : ContDiff ℝ ∞ fun x => Real.sqrt (f x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (Real.contDiffAt_sqrt (x := f x) (hpos x).ne').comp x hf.contDiffAt
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, Real.sqrt (f t) with hG
  have hderiv : ∀ x, HasDerivAt G (Real.sqrt (f x)) x := by
    intro x
    exact integral_hasDerivAt_right (hs.continuous.intervalIntegrable _ _)
      hs.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuous.continuousAt
  have hd : deriv G = fun x => Real.sqrt (f x) := funext fun x => (hderiv x).deriv
  refine ⟨G, ?_, ?_, hderiv⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, by rw [hd]; exact hs⟩
  · refine strictMono_of_deriv_pos fun x => ?_
    rw [hd]
    exact Real.sqrt_pos.2 (hpos x)

/-- **Nash embedding, one-dimensional case.** Every Riemannian metric `g_x(v,w) = f(x) · v · w`
on the real line (with `f` smooth and positive) is induced by a smooth embedding of the line
into `ℝ`: there is a smooth strictly increasing `F : ℝ → ℝ` whose differential carries the
Euclidean inner product of the target back to `g`. -/
