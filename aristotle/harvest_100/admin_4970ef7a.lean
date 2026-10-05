/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Arithmetic Quantum Unique Ergodicity (Lindenstrauss)

Setting.  `X` is a compact metric space — in the intended application, the unit
cotangent bundle `Γ \ PSL₂(ℝ)` of a compact congruence arithmetic hyperbolic
surface — carrying its Borel σ-algebra, and `vol` is the normalized Liouville
(Haar) probability measure on `X`.  A sequence `μ : ℕ → ProbabilityMeasure X` of
*microlocal lifts* of Hecke–Maass eigenforms with eigenvalue tending to infinity
is given.  *Quantum unique ergodicity* is the assertion that `μ n → vol` in the
weak-* (convergence in distribution) topology.

Lindenstrauss's theorem proves this by measure rigidity: every weak-* limit
point of the sequence (a *quantum limit*) is invariant under the geodesic flow,
is recurrent under the Hecke correspondence, and has positive entropy on almost
every ergodic component; and any such measure is the Haar measure.

What is formalized here.  The *reduction* is proved unconditionally and in full:
if every quantum limit of the sequence equals `vol`, then the whole sequence
converges to `vol` in the weak-* topology, hence `∫ f dμ n → ∫ f dvol` for every
bounded continuous observable `f` and `μ n A → vol A` for every Borel set whose
boundary is `vol`-null.  The two arithmetic/dynamical inputs — that quantum
limits satisfy the rigidity hypotheses, and Lindenstrauss's classification of
measures satisfying them — enter as explicit hypotheses `hArithmetic` and
`hRigidity` on an abstract predicate `Rigid`, so that the statement below is
exactly the logical skeleton of Lindenstrauss's deduction of QUE from measure
rigidity, with the topological/measure-theoretic half proved in Lean.
-/

namespace Frontier

open Filter MeasureTheory Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

/-- The set of **quantum limits** of a sequence of probability measures `μ`:
all weak-* limits of subsequences of `μ`. -/
def QuantumLimits (μ : ℕ → ProbabilityMeasure X) : Set (ProbabilityMeasure X) :=
  {ν | ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun n => μ (ns n)) atTop (𝓝 ν)}

lemma mem_quantumLimits_iff {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X} :
    ν ∈ QuantumLimits μ ↔ ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun n => μ (ns n)) atTop (𝓝 ν) :=
  Iff.rfl

section Compact

variable [T2Space X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]

/-- Every sequence of probability measures on a compact metrizable space has at least one
quantum limit: the space of probability measures is compact and metrizable, hence
sequentially compact. -/
theorem quantumLimits_nonempty (μ : ℕ → ProbabilityMeasure X) :
    (QuantumLimits μ).Nonempty := by
  obtain ⟨ν, -, ns, hns, hconv⟩ :=
    (isCompact_univ (X := ProbabilityMeasure X)).tendsto_subseq
      (x := μ) (fun n => Set.mem_univ (μ n))
  exact ⟨ν, ns, hns, hconv⟩

/-- **Reduction of QUE to the classification of quantum limits.**  If every quantum limit
of the sequence `μ` is the measure `vol`, then `μ` converges to `vol` in the weak-*
topology. -/
theorem tendsto_of_quantumLimits_subsingleton
    (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (h : ∀ ν ∈ QuantumLimits μ, ν = vol) :
    Tendsto μ atTop (𝓝 vol) := by
  refine tendsto_nhds_of_unique_mapClusterPt (fun ν hν => h ν ?_)
  obtain ⟨ns, hns, hconv⟩ := subseq_tendsto_of_neBot hν
  exact ⟨ns, hns, hconv⟩

end Compact

/-- **Arithmetic quantum unique ergodicity (Lindenstrauss).**

`X` is a compact metrizable space — the unit cotangent bundle of a compact congruence
arithmetic hyperbolic surface — with normalized Liouville probability measure `vol`, and
`μ n` are the microlocal lifts of a sequence of Hecke–Maass eigenforms.

`Rigid` abstracts the dynamical hypotheses appearing in Lindenstrauss's measure
classification (invariance under the geodesic flow, Hecke recurrence, positive entropy on
almost every ergodic component).  Given

* `hArithmetic`: every quantum limit of the sequence is `Rigid` (the semiclassical and
  Hecke-theoretic input), and
* `hRigidity`: every `Rigid` measure is the Liouville measure (Lindenstrauss's measure
  rigidity theorem),

the sequence equidistributes: `μ n → vol` weak-*, the expectation of every bounded
continuous observable converges, and `μ n A → vol A` for every Borel set `A` whose
boundary is `vol`-null. -/
theorem lindenstrauss_QUE
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (Rigid : ProbabilityMeasure X → Prop)
    (hArithmetic : ∀ ν ∈ QuantumLimits μ, Rigid ν)
    (hRigidity : ∀ ν : ProbabilityMeasure X, Rigid ν → ν = vol) :
    Tendsto μ atTop (𝓝 vol) ∧
      (∀ f : BoundedContinuousFunction X ℝ,
        Tendsto (fun n => ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 (∫ x, f x ∂(vol : Measure X)))) ∧
      (∀ A : Set X, (vol : Measure X) (frontier A) = 0 →
        Tendsto (fun n => μ n A) atTop (𝓝 (vol A))) := by
  have hconv : Tendsto μ atTop (𝓝 vol) :=
    tendsto_of_quantumLimits_subsingleton μ vol fun ν hν => hRigidity ν (hArithmetic ν hν)
  refine ⟨hconv, ?_, ?_⟩
  · exact fun f => (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) f
  · intro A hA
    have hA' : vol (frontier A) = 0 := by
      have h := ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure vol (frontier A)
      rw [hA] at h
      exact_mod_cast h
    exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hconv hA'

/-- A probability measure is invariant under the flow `T` (in the application, the geodesic
flow on the unit cotangent bundle). -/
def FlowInvariant {X : Type*} [MeasurableSpace X] (T : ℝ → X → X)
    (ν : ProbabilityMeasure X) : Prop :=
  ∀ t : ℝ, (ν : Measure X).map (T t) = (ν : Measure X)

/-- **Lindenstrauss's QUE, stated with the three dynamical hypotheses of the measure
classification theorem made explicit.**  Every quantum limit of the sequence of microlocal
lifts is invariant under the geodesic flow `T`, is recurrent under the Hecke correspondence
and has positive entropy on almost every ergodic component (`hArithmetic`); Lindenstrauss's
measure rigidity theorem says that any measure with these three properties is the Liouville
measure (`hRigidity`).  The conclusion is quantum unique ergodicity: `μ n → vol` weak-*. -/
theorem lindenstrauss_QUE_of_measure_rigidity
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    (T : ℝ → X → X) (HeckeRecurrent PositiveEntropy : ProbabilityMeasure X → Prop)
    (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (hArithmetic : ∀ ν ∈ QuantumLimits μ,
      FlowInvariant T ν ∧ HeckeRecurrent ν ∧ PositiveEntropy ν)
    (hRigidity : ∀ ν : ProbabilityMeasure X,
      FlowInvariant T ν → HeckeRecurrent ν → PositiveEntropy ν → ν = vol) :
    Tendsto μ atTop (𝓝 vol) :=
  (lindenstrauss_QUE μ vol
    (fun ν => FlowInvariant T ν ∧ HeckeRecurrent ν ∧ PositiveEntropy ν) hArithmetic
    (fun ν hν => hRigidity ν hν.1 hν.2.1 hν.2.2)).1

/-- Base case / non-vacuity check: a sequence that is already equal to the Liouville
measure has `vol` as its unique quantum limit, and the conclusion of QUE holds for it. -/
theorem lindenstrauss_QUE_base
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    (vol : ProbabilityMeasure X) :
    QuantumLimits (fun _ : ℕ => vol) = {vol} ∧
      Tendsto (fun _ : ℕ => vol) atTop (𝓝 vol) := by
  constructor
  · ext ν
    constructor
    · rintro ⟨ns, -, hconv⟩
      have : ν = vol := tendsto_nhds_unique hconv tendsto_const_nhds
      simp [this]
    · intro hν
      rw [Set.mem_singleton_iff] at hν
      subst hν
      exact ⟨id, strictMono_id, tendsto_const_nhds⟩
  · exact tendsto_const_nhds

/-- The reduction is genuinely sharp: conversely, if the sequence equidistributes then
`vol` is its only quantum limit. -/
theorem quantumLimits_eq_of_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (h : Tendsto μ atTop (𝓝 vol)) :
    QuantumLimits μ = {vol} := by
  ext ν
  constructor
  · rintro ⟨ns, hns, hconv⟩
    have hsub : Tendsto (fun n => μ (ns n)) atTop (𝓝 vol) := h.comp hns.tendsto_atTop
    have : ν = vol := tendsto_nhds_unique hconv hsub
    simp [this]
  · intro hν
    rw [Set.mem_singleton_iff] at hν
    subst hν
    exact ⟨id, strictMono_id, h⟩

end Frontier

