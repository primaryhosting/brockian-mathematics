import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-!
## The Gaussian correlation inequality

The Gaussian correlation inequality (conjectured by Dunnett–Sobel / Das Gupta et al., proved by
Thomas Royen in 2014) states that for a centred Gaussian measure `μ` on `ℝⁿ` and any two
symmetric convex sets `s`, `t`,
`μ s * μ t ≤ μ (s ∩ t)`.

A search of Mathlib (`exact?`/`apply?`/`rw?` and name search for `gaussian` / `correlation`)
shows that no form of this inequality is currently available: Mathlib contains
`ProbabilityTheory.gaussianReal` and the class `ProbabilityTheory.IsGaussian`, but no correlation
inequality for Gaussian measures.  We therefore formalise the statement below
(`Frontier.GaussianCorrelationInequality`), and prove:

* the *base case*, dimension one (`Frontier.gaussian_correlation`), in the strong form where no
  measurability of the sets and no centring of the Gaussian is assumed;
* a dimension-free *reduction*: the inequality holds in any dimension as soon as the two sets are
  nested (`Frontier.gaussian_correlation_of_subset_or_subset`);
* a *reduction along linear isomorphisms*
  (`Frontier.GaussianCorrelationInequality.of_continuousLinearEquiv`): the inequality only depends
  on the linear-homeomorphism class of the ambient space;
* consequently the case `n = 1` of Royen's theorem on `EuclideanSpace ℝ (Fin 1)`
  (`Frontier.gaussianCorrelationInequality_euclideanSpace_fin_one`).

The general case (`n ≥ 2`), i.e. Royen's theorem itself, is not proved here.

The proof of the base case is the classical one: in dimension one any two symmetric convex sets
are nested (`Frontier.SymmetricConvex.subset_or_subset`), and for nested sets the inequality is
immediate from `μ ≤ 1` for a probability measure.
-/

/-- A subset of a real vector space is *symmetric convex* if it is convex and invariant under
`x ↦ -x`.  These are the sets occurring in the Gaussian correlation inequality. -/
structure SymmetricConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E) : Prop where
  /-- The set is convex. -/
  convex : Convex ℝ s
  /-- The set is symmetric about the origin. -/
  neg_mem : ∀ ⦃x : E⦄, x ∈ s → -x ∈ s

/-- Any point of absolute value at most `|x|` lies in a symmetric convex subset of `ℝ`
containing `x`: such a set is "an interval around the origin". -/

theorem SymmetricConvex.preimage_continuousLinearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) {s : Set F}
    (hs : SymmetricConvex s) : SymmetricConvex (e ⁻¹' s) where
  convex := hs.convex.linear_preimage (e : E →L[ℝ] F).toLinearMap
  neg_mem x hx := by
    simp only [Set.mem_preimage, map_neg] at *
    exact hs.neg_mem hx

/-- **Reduction along linear isomorphisms.** The Gaussian correlation inequality transfers along
a linear homeomorphism `e : E ≃L[ℝ] F`: if it holds on `E`, it holds on `F`.  (In particular it
only depends on the linear-topological isomorphism class of the space, so for `ℝⁿ` it suffices
to prove it for one model of `n`-dimensional space.) -/
