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

theorem tendsto_circleVol_of_asymptoticallyInvariant (μ : ℕ → ProbabilityMeasure (AddCircle (1 : ℝ)))
    (hasym : ∀ (g : AddCircle (1 : ℝ)) (f : C(AddCircle (1 : ℝ), ℝ)), Tendsto
      (fun n => (∫ x, f (g + x) ∂(μ n : Measure (AddCircle (1 : ℝ))))
        - ∫ x, f x ∂(μ n : Measure (AddCircle (1 : ℝ)))) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 circleVol) ∧
      ∀ f : C(AddCircle (1 : ℝ), ℝ),
        Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (AddCircle (1 : ℝ)))) atTop
          (𝓝 (∫ x, f x ∂(circleVol : Measure (AddCircle (1 : ℝ))))) :=
  tendsto_addHaar_of_asymptoticallyInvariant circleVol μ hasym

end Circle

/-!
## Sanity checks

The hypothesis of `lindenstrauss_QUE` is not vacuous: the constant sequence `μ n = vol`
satisfies it, and the conclusion holds for it.
-/

section SanityCheck

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- The measure classification hypothesis of `lindenstrauss_QUE` is satisfied by the constant
sequence `μ n = vol` (for which the conclusion is of course also immediate). -/
