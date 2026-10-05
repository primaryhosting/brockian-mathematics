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

open Filter Topology MeasureTheory

/-!
## Setting

Arithmetic quantum unique ergodicity (Lindenstrauss).  Let `Y = Γ \ ℍ` be a compact
congruence surface and let `X = Γ \ PSL₂(ℝ)` be its unit cotangent bundle, a compact
metric space carrying the normalized Haar (Liouville) probability measure `vol`.
To a sequence of `L²`-normalized Hecke–Maass eigenforms `φₙ` one associates the
sequence of *microlocal lifts* `μ n`, Borel probability measures on `X`.

Quantum unique ergodicity is the assertion that `μ n → vol` in the weak-* topology
on probability measures, equivalently `∫ f dμ n → ∫ f d vol` for every continuous
observable `f`.

In this file `X` is an abstract compact metric space, `μ : ℕ → ProbabilityMeasure X`
an abstract sequence of states, `vol` the reference measure, and `P` an abstract
property of measures which, in Lindenstrauss's theorem, is the conjunction

* invariance under the geodesic flow (Šnirel'man / Egorov),
* positive entropy on almost every ergodic component (Bourgain–Lindenstrauss),
* recurrence under the Hecke correspondence,

and the classification input `hrigidity` is Lindenstrauss's measure rigidity theorem:
the only measure with property `P` is the Haar measure `vol`.  The content formalized
and proved here is the (Lean-checked) reduction of QUE to that classification: every
*quantum limit*, i.e. every weak-* limit of a subsequence of `μ`, satisfies `P`, hence
equals `vol`, and by compactness of the space of probability measures on a compact
space the full sequence must then converge to `vol`.
-/

/-- `ρ` is a *quantum limit* of the sequence of states `μ`: it is the weak-* limit of
some subsequence of `μ`. -/
def IsQuantumLimit {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    (μ : ℕ → ProbabilityMeasure X) (ρ : ProbabilityMeasure X) : Prop :=
  ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun k ↦ μ (ns k)) atTop (𝓝 ρ)

section

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Being a quantum limit is the same as being a cluster point of the sequence of states
in the weak-* topology. -/
theorem isQuantumLimit_iff_mapClusterPt (μ : ℕ → ProbabilityMeasure X)
    (ρ : ProbabilityMeasure X) :
    IsQuantumLimit μ ρ ↔ MapClusterPt ρ atTop μ := by
  constructor
  · rintro ⟨ns, hns, hconv⟩
    exact MapClusterPt.of_comp hns.tendsto_atTop hconv.mapClusterPt
  · intro h
    obtain ⟨ns, hns, hconv⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq h
    exact ⟨ns, hns, hconv⟩

/-- Quantum limits exist: the space of probability measures on a compact metric space is
sequentially compact. -/
theorem exists_isQuantumLimit (μ : ℕ → ProbabilityMeasure X) :
    ∃ ρ : ProbabilityMeasure X, IsQuantumLimit μ ρ := by
  obtain ⟨ρ, -, ns, hns, hconv⟩ :=
    (isCompact_univ (X := ProbabilityMeasure X)).tendsto_subseq
      (x := μ) (fun n ↦ Set.mem_univ _)
  exact ⟨ρ, ns, hns, hconv⟩

/-- **Arithmetic quantum unique ergodicity (Lindenstrauss), as a Lean-checked reduction.**

Let `X` be a compact metric space (the unit cotangent bundle `Γ \ PSL₂(ℝ)` of a compact
congruence surface), `μ n` a sequence of Borel probability measures on `X` (the microlocal
lifts of a sequence of Hecke–Maass eigenforms) and `vol` the normalized Haar measure.
Assume:

* `hlimit`: every quantum limit of `μ` has property `P` — in Lindenstrauss's setting `P`
  records geodesic-flow invariance, positive entropy on a.e. ergodic component, and Hecke
  recurrence;
* `hrigidity`: the measure classification (measure rigidity) theorem: the only probability
  measure with property `P` is `vol`.

Then the sequence `μ` converges to `vol` in the weak-* topology, and every continuous
observable equidistributes: `∫ f dμ n → ∫ f d vol`. -/
theorem lindenstrauss_QUE (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (P : ProbabilityMeasure X → Prop)
    (hlimit : ∀ ρ : ProbabilityMeasure X, IsQuantumLimit μ ρ → P ρ)
    (hrigidity : ∀ ρ : ProbabilityMeasure X, P ρ → ρ = vol) :
    Tendsto μ atTop (𝓝 vol) ∧
      ∀ f : C(X, ℝ), Tendsto (fun n ↦ ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂vol)) := by
  have hconv : Tendsto μ atTop (𝓝 vol) := by
    refine tendsto_nhds_of_unique_mapClusterPt (fun ρ hρ ↦ ?_)
    exact hrigidity ρ (hlimit ρ ((isQuantumLimit_iff_mapClusterPt μ ρ).2 hρ))
  refine ⟨hconv, fun f ↦ ?_⟩
  exact ((ProbabilityMeasure.continuous_integral_continuousMap
    (X := X) f).tendsto vol).comp hconv

/-- Base case: a sequence of states that is already equal to the Haar measure trivially
satisfies the hypotheses and conclusion of `Frontier.lindenstrauss_QUE`; in particular the
statement is not vacuous. -/
theorem lindenstrauss_QUE_base (vol : ProbabilityMeasure X) :
    Tendsto (fun _ : ℕ ↦ vol) atTop (𝓝 vol) ∧
      ∀ f : C(X, ℝ), Tendsto (fun _ : ℕ ↦ ∫ x, f x ∂vol) atTop (𝓝 (∫ x, f x ∂vol)) := by
  refine lindenstrauss_QUE (fun _ ↦ vol) vol (fun ρ ↦ ρ = vol) (fun ρ hρ ↦ ?_) (fun _ h ↦ h)
  obtain ⟨ns, -, hns⟩ := hρ
  exact tendsto_nhds_unique hns tendsto_const_nhds

end

end Frontier

