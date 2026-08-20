import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Frontier

open ProbabilityTheory

/-- The Gaussian correlation inequality, as a property of a measure `μ` on a real vector
space `E`:  for any two measurable, convex, origin-symmetric sets `K` and `L`,
`μ (K ∩ L) ≥ μ K * μ L`.

Royen's theorem states that this holds for every centred Gaussian measure `μ`.  In this file
we formalise the statement and prove the one-dimensional base case together with several
Lean-checked reductions. -/

def RoyenGaussianCorrelation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ μ : Measure E, IsGaussian μ → μ.map (fun x => -x) = μ → GaussianCorrelation μ

/-- Reduction: for a probability measure, the correlation inequality holds for any pair of
nested sets.  (No convexity, symmetry or Gaussianity is needed.) -/
