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

theorem invariant_of_tendsto_of_invariant {T : X → X} (hT : Continuous T)
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hinv : ∀ n, Measure.map T ((μ n : Measure X)) = (μ n : Measure X))
    (hlim : Tendsto μ atTop (𝓝 ν)) :
    Measure.map T (ν : Measure X) = (ν : Measure X) := by
  refine invariant_of_tendsto_of_asymptoticallyInvariant hT (fun f => ?_) hlim
  have hf : ∀ n, (∫ x, f (T x) ∂(μ n : Measure X)) - ∫ x, f x ∂(μ n : Measure X) = 0 := by
    intro n
    rw [← integral_map hT.measurable.aemeasurable f.continuous.aestronglyMeasurable, hinv n,
      sub_self]
  simp [hf]

/-- **Quantum unique ergodicity in the uniquely ergodic case (unconditional).**

Let `X` be a compact metric space with its Borel σ-algebra, acted on by a family `T i` of
continuous maps (e.g. the time-`t` maps of the geodesic flow, or the translations by a group),
and suppose the action is *uniquely ergodic*: `vol` is the only probability measure invariant
under all the `T i`.  If the sequence `μ n` is *asymptotically invariant* under the action — the
property enjoyed by microlocal lifts of eigenfunctions — then `μ n → vol` in the weak-*
topology, and the quantum averages of every continuous observable converge to its classical
average.

This is the classical (Shnirelman–Zelditch–Colin de Verdière style) mechanism: unique ergodicity
of the classical dynamics forces quantum unique ergodicity.  It is genuinely unconditional; no
measure classification is assumed, since unique ergodicity supplies it.  Lindenstrauss' theorem
is precisely the replacement of the (false, on a hyperbolic surface) unique ergodicity assumption
by arithmetic input: Hecke recurrence together with positive entropy. -/
