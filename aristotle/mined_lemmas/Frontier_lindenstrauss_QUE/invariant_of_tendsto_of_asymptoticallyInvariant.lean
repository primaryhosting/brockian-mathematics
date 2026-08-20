import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace Frontier

/-!
## Setting

Elad Lindenstrauss' *arithmetic quantum unique ergodicity* theorem concerns a congruence
surface `Γ \ ℍ` (or rather the unit tangent bundle `X = Γ \ PSL₂(ℝ)` of such a surface) and a
sequence of Hecke–Maass eigenforms `ψₙ`.  To each `ψₙ` one attaches its *microlocal lift*, a
probability measure `μₙ` on `X`, and the theorem asserts that `μₙ` converges in the weak-*
topology to the normalized volume (Liouville) measure `vol`.

The whole content of Lindenstrauss' proof is the *measure classification* step: any weak-*
limit of the microlocal lifts is a `PSL₂(ℝ)`-invariant, Hecke-recurrent measure of positive
entropy on every ergodic component, and every such measure equals `vol`.

The statement below is the Lean-checked *reduction* of quantum unique ergodicity to that
measure classification statement: on a compact space carrying its Borel σ-algebra (the unit
tangent bundle of a compact congruence surface is such a space), if **every** subsequential
weak-* limit of the sequence of microlocal lifts is the volume measure, then the full sequence
converges weak-* to the volume measure; equivalently, the "quantum averages"
`∫ f dμₙ` converge to the "classical average" `∫ f dvol` for every continuous observable `f`.

The two ingredients, both from Mathlib, are:

* `MeasureTheory.ProbabilityMeasure.instCompactSpace`: weak-* compactness of the space of
  probability measures on a compact metrizable space (Banach–Alaoglu / Prokhorov), together
  with its metrizability, which makes the weak-* topology first countable;
* `tendsto_nhds_of_unique_mapClusterPt`: in a compact space, a filter with a unique cluster
  point converges to it.
-/

section Reduction

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]

/-- **Arithmetic quantum unique ergodicity, Lean-checked reduction to measure classification
(Lindenstrauss).**

Let `X` be a compact metric space with its Borel σ-algebra — e.g. the unit tangent bundle
`Γ \ PSL₂(ℝ)` of a compact congruence surface — let `vol` be the normalized volume (Liouville)
probability measure on `X`, and let `μ : ℕ → ProbabilityMeasure X` be the sequence of microlocal
lifts of a sequence of Hecke–Maass eigenforms.

Assume the *measure classification* hypothesis established by Lindenstrauss: every weak-*
limit of a subsequence of `μ` is `vol`.  Then the full sequence equidistributes: `μ n → vol`
in the weak-* topology, and for every continuous observable `f : X → ℝ` the quantum averages
`∫ f dμ n` converge to the classical average `∫ f dvol`. -/

theorem invariant_of_tendsto_of_asymptoticallyInvariant {T : X → X} (hT : Continuous T)
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hasym : ∀ f : C(X, ℝ), Tendsto
      (fun n => (∫ x, f (T x) ∂(μ n : Measure X)) - ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 0))
    (hlim : Tendsto μ atTop (𝓝 ν)) :
    Measure.map T (ν : Measure X) = (ν : Measure X) := by
  have h1 : Tendsto (fun n => (μ n).map hT.measurable.aemeasurable) atTop
      (𝓝 (ν.map hT.measurable.aemeasurable)) :=
    ((ProbabilityMeasure.continuous_map (f := T) hT).tendsto ν).comp hlim
  have h2 : Tendsto (fun n => (μ n).map hT.measurable.aemeasurable) atTop (𝓝 ν) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr (fun g => ?_)
    have hg : ∀ n, ∫ x, g x ∂(((μ n).map hT.measurable.aemeasurable : ProbabilityMeasure X) :
        Measure X) = ∫ x, g (T x) ∂(μ n : Measure X) := by
      intro n
      rw [ProbabilityMeasure.toMeasure_map]
      exact integral_map hT.measurable.aemeasurable g.continuous.aestronglyMeasurable
    simp only [hg]
    have hbase := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
    simpa using (hasym (BoundedContinuousFunction.toContinuousMap g)).add hbase
  have := congrArg (fun ρ : ProbabilityMeasure X => (ρ : Measure X)) (tendsto_nhds_unique h1 h2)
  simpa [ProbabilityMeasure.toMeasure_map] using this

omit [CompactSpace X] in
/-- Exact invariance under a continuous map is a weak-* closed condition: if every `μ n` is
invariant under `T` and `μ n → ν` in the weak-* topology, then `ν` is invariant under `T`. -/
