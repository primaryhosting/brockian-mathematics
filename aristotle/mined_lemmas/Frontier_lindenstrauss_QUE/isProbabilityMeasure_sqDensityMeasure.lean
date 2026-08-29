import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

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

namespace Frontier

open MeasureTheory Filter Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Weak-\* compactness reduction.**  If every subsequential weak-\* limit of a sequence of
probability measures on a compact metric space equals `vol`, then the whole sequence converges
weak-\* to `vol`. -/

lemma isProbabilityMeasure_sqDensityMeasure (vol : Measure X) [IsProbabilityMeasure vol]
    (f : C(X, ℝ)) (hf : ∫ x, f x ^ 2 ∂vol = 1) :
    IsProbabilityMeasure (sqDensityMeasure vol f) := by
  constructor
  have hint : Integrable (fun x => f x ^ 2) vol :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [sqDensityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hlint : ∫⁻ x, (Real.toNNReal (f x ^ 2) : ℝ≥0∞) ∂vol = ENNReal.ofReal (∫ x, f x ^ 2 ∂vol) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    rfl
  rw [hlint, hf, ENNReal.ofReal_one]

/-- **Arithmetic Quantum Unique Ergodicity (Lindenstrauss), in reduced form.**

Setting: a compact metric space `X` (the congruence surface, or its unit cotangent bundle)
carrying a normalised volume measure `vol`, and a sequence `phi` of `L²`-normalised real
functions (the Hecke–Maass eigenfunctions).

Hypothesis `hQL` is exactly the classification of quantum limits which is the content of
Lindenstrauss' theorem: every weak-\* limit `ν` of the sequence of microlocal lifts
`|phi n|² vol` along a subsequence is the normalised volume measure.

Conclusion: the full sequence of probability densities `|phi n|²` equidistributes, i.e.
`∫ g |phi n|² dvol → ∫ g dvol` for every continuous observable `g`.

The proof is the weak-\* compactness argument reducing QUE to the classification of quantum
limits. -/
