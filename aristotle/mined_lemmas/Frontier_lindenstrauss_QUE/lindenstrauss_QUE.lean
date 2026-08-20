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

theorem lindenstrauss_QUE (vol : ProbabilityMeasure X) (μ : ℕ → ProbabilityMeasure X)
    (measure_classification : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ ν : ProbabilityMeasure X,
      Tendsto (fun n => μ (φ n)) atTop (𝓝 ν) → ν = vol) :
    Tendsto μ atTop (𝓝 vol) ∧
      ∀ f : C(X, ℝ), Tendsto (fun n => ∫ x, f x ∂(μ n : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(vol : Measure X))) := by
  -- Weak-* convergence: the space of probability measures on `X` is compact and metrizable,
  -- so it suffices to know that `vol` is the unique cluster point of the sequence `μ`.
  have hconv : Tendsto μ atTop (𝓝 vol) := by
    refine tendsto_nhds_of_unique_mapClusterPt (fun ν hν => ?_)
    obtain ⟨φ, hφ, hlim⟩ := FirstCountableTopology.tendsto_subseq hν
    exact measure_classification φ hφ ν hlim
  refine ⟨hconv, fun f => ?_⟩
  -- Convergence of the integrals of continuous observables: on a compact space every
  -- continuous function is bounded, so this is the definition of weak-* convergence.
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
    (BoundedContinuousFunction.mkOfCompact f)
  simpa using this

end Reduction

/-!
## The dynamical input: invariance passes to weak-* limits, and the uniquely ergodic case

The results in this section are *unconditional*.  They isolate the elementary half of the QUE
mechanism: the microlocal lifts `μₙ` are (asymptotically) invariant under the geodesic flow, and
invariance is a weak-* closed condition, so every subsequential limit is flow invariant.  If the
flow — or, more generally, the acting group — admits only one invariant probability measure
(unique ergodicity), the measure classification hypothesis of `lindenstrauss_QUE` is *automatic*
and quantum unique ergodicity follows outright.  Lindenstrauss' theorem is exactly the statement
that, on a congruence surface, the extra arithmetic information (Hecke recurrence plus positive
entropy) can substitute for unique ergodicity, which fails there because of the closed geodesics.
-/

section Dynamics

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- *Asymptotic* invariance also passes to weak-* limits.  This is the form in which the
hypothesis is available for microlocal lifts: `μ n` need not be exactly invariant under the
geodesic flow, only invariant in the limit, i.e. `∫ f ∘ T dμ n - ∫ f dμ n → 0` for every
continuous observable `f`.  Any weak-* limit `ν` of such a sequence is exactly `T`-invariant. -/
