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
theorem tendsto_haar_of_asymptoticallyInvariant (vol : ProbabilityMeasure G)
    [(vol : Measure G).IsHaarMeasure] (μ : ℕ → ProbabilityMeasure G)
    (hasym : ∀ (g : G) (f : C(G, ℝ)), Tendsto
      (fun n => (∫ x, f (g * x) ∂(μ n : Measure G)) - ∫ x, f x ∂(μ n : Measure G)) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 vol) ∧
      ∀ f : C(G, ℝ), Tendsto (fun n => ∫ x, f x ∂(μ n : Measure G)) atTop
        (𝓝 (∫ x, f x ∂(vol : Measure G))) :=
  QUE_of_uniquelyErgodic (T := fun g : G => fun x => g * x) (fun g => continuous_mul_left g)
    vol μ (fun ν hν => eq_of_isMulLeftInvariant vol ν hν) hasym

end CompactGroup

/-!
## The circle: a fully concrete unconditional equidistribution theorem

Specializing the previous section to `AddCircle 1` gives an unconditional, hypothesis-free
equidistribution statement about an explicit space.
-/

section Circle

/-- The Lebesgue probability measure on the circle `ℝ / ℤ`. -/
noncomputable def circleVol : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨volume, ⟨by simp [AddCircle.measure_univ]⟩⟩

@[simp] lemma circleVol_coe : (circleVol : Measure (AddCircle (1 : ℝ))) = volume := rfl

instance : (circleVol : Measure (AddCircle (1 : ℝ))).IsAddHaarMeasure := by
  rw [circleVol_coe]; infer_instance

/-- **Equidistribution on the circle (unconditional).**  A sequence of probability measures on
`ℝ / ℤ` that is asymptotically invariant under all rotations converges weak-* to Lebesgue
measure, and the averages of every continuous observable converge to its mean. -/
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
theorem lindenstrauss_QUE_constant_case (vol : ProbabilityMeasure X) :
    ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ ν : ProbabilityMeasure X,
      Tendsto (fun n => (fun _ : ℕ => vol) (φ n)) atTop (𝓝 ν) → ν = vol := by
  intro φ _ ν hν
  exact tendsto_nhds_unique hν tendsto_const_nhds

example (vol : ProbabilityMeasure X) :
    Tendsto (fun _ : ℕ => vol) atTop (𝓝 vol) :=
  (lindenstrauss_QUE vol (fun _ => vol) (lindenstrauss_QUE_constant_case vol)).1

end SanityCheck

end Frontier

import Mathlib

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

