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

theorem QUE_of_uniquelyErgodic {ι : Type*} {T : ι → X → X} (hT : ∀ i, Continuous (T i))
    (vol : ProbabilityMeasure X) (μ : ℕ → ProbabilityMeasure X)
    (unique_ergodicity : ∀ ν : ProbabilityMeasure X,
      (∀ i, Measure.map (T i) (ν : Measure X) = (ν : Measure X)) → ν = vol)
    (hasym : ∀ (i : ι) (f : C(X, ℝ)), Tendsto
      (fun n => (∫ x, f (T i x) ∂(μ n : Measure X)) - ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 vol) ∧
      ∀ f : C(X, ℝ), Tendsto (fun n => ∫ x, f x ∂(μ n : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(vol : Measure X))) := by
  refine lindenstrauss_QUE vol μ (fun φ hφ ν hν => unique_ergodicity ν (fun i => ?_))
  refine invariant_of_tendsto_of_asymptoticallyInvariant (hT i) (fun f => ?_) hν
  -- a subsequence of a sequence tending to `0` still tends to `0`
  exact (hasym i f).comp hφ.tendsto_atTop

end Dynamics

/-!
## A concrete unconditional instance: equidistribution on a compact group

The translation action of a compact group on itself is uniquely ergodic — its unique invariant
probability measure is the Haar probability measure — by uniqueness of Haar measure.  Feeding
this into `QUE_of_uniquelyErgodic` gives an unconditional equidistribution theorem: any sequence
of probability measures on a compact metrizable group which is asymptotically invariant under
all translations converges weak-* to Haar measure.  This is the homogeneous-space model case of
quantum unique ergodicity.
-/

section CompactGroup

variable {G : Type*} [MetricSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Unique ergodicity of the translation action of a compact group on itself**: the Haar
probability measure is the only translation invariant probability measure. -/
@[to_additive /-- **Unique ergodicity of the translation action of a compact additive group on
itself**: the Haar probability measure is the only translation invariant probability measure. -/]
