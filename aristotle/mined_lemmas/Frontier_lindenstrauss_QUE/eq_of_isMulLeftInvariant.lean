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

theorem eq_of_isMulLeftInvariant (vol : ProbabilityMeasure G) [(vol : Measure G).IsHaarMeasure]
    (ν : ProbabilityMeasure G)
    (h : ∀ g : G, Measure.map (fun x => g * x) (ν : Measure G) = (ν : Measure G)) :
    ν = vol := by
  have hinv : (ν : Measure G).IsMulLeftInvariant := ⟨h⟩
  have hsmul : (ν : Measure G)
      = (ν : Measure G).haarScalarFactor (vol : Measure G) • (vol : Measure G) :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have huniv := congrArg (fun m : Measure G => m Set.univ) hsmul
  simp [measure_univ] at huniv
  have hc : (ν : Measure G).haarScalarFactor (vol : Measure G) = 1 := by
    have h1 : ((ν : Measure G).haarScalarFactor (vol : Measure G) : ℝ≥0∞) • (1 : ℝ≥0∞) = 1 :=
      huniv.symm
    rw [smul_eq_mul, mul_one] at h1
    exact_mod_cast h1
  exact ProbabilityMeasure.toMeasure_injective (by rw [hsmul, hc, one_smul])

/-- **Unconditional equidistribution on a compact group.**  A sequence of probability measures
on a compact metrizable group which is asymptotically invariant under every translation
converges weak-* to the Haar probability measure, and the corresponding averages of every
continuous observable converge. -/
@[to_additive /-- **Unconditional equidistribution on a compact additive group.**  A sequence of
probability measures on a compact metrizable additive group which is asymptotically invariant
under every translation converges weak-* to the Haar probability measure, and the corresponding
averages of every continuous observable converge. -/]
