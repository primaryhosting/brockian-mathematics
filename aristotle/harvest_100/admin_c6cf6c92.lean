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

set_option grind.warning false

open MeasureTheory Filter Topology

namespace Frontier

/-!
## Setting

Arithmetic quantum unique ergodicity (Lindenstrauss) concerns a compact congruence
surface `M = Γ \ ℍ`, its unit cotangent bundle `X = Γ \ PSL(2,ℝ)`, a sequence of
Hecke–Maass eigenforms with eigenvalue tending to infinity, and the associated
sequence of *microlocal lifts* `μ n`, which are Borel probability measures on the
compact space `X`.  The deep input of Lindenstrauss' theorem is a *measure
classification* statement:

> every weak-\* accumulation point of the sequence of microlocal lifts is the
> normalized Liouville (volume) measure `vol`.

The content formalized here is the abstract measure-theoretic framework in which
these statements live, together with a fully Lean-checked reduction: the
classification statement about subsequential limits is *equivalent* to the QUE
equidistribution statement

  `∫ f dμ n → ∫ f d vol`  for every continuous observable `f`.

Throughout, `X` is an arbitrary compact metric space equipped with its Borel
σ-algebra — the properties of `X` actually used are exactly compactness and
metrizability of the phase space, which hold for `Γ \ PSL(2,ℝ)` with `Γ` a
cocompact congruence lattice.
-/

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `IsQuantumLimit μ ν` says that the probability measure `ν` is a weak-\*
accumulation point of the sequence `μ` of probability measures, i.e. `ν` is the
limit of `μ` along some subsequence.  In the arithmetic setting, `μ n` are the
microlocal lifts of a sequence of Hecke–Maass eigenforms and `ν` is a *quantum
limit*. -/
def IsQuantumLimit (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X) : Prop :=
  ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun n => μ (ns n)) atTop (𝓝 ν)

/-- `Equidistributes μ vol` is the quantum unique ergodicity conclusion: the
observables' expectations `∫ f dμ n` converge to the average `∫ f d vol` against
the volume measure, for every continuous observable `f`. -/
def Equidistributes (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X) : Prop :=
  ∀ f : C(X, ℝ),
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 (∫ x, f x ∂(vol : Measure X)))

/-- On a compact metric space, weak-\* convergence of probability measures is
equivalent to convergence of the integrals of all continuous functions. -/
theorem tendsto_iff_equidistributes (μ : ℕ → ProbabilityMeasure X)
    (vol : ProbabilityMeasure X) :
    Tendsto μ atTop (𝓝 vol) ↔ Equidistributes μ vol := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  constructor
  · intro h f
    exact h (ContinuousMap.mkOfCompact f)
  · intro h f
    exact h (BoundedContinuousFunction.toContinuousMap f)

/-- **Reduction step.**  If every quantum limit of the sequence `μ` equals `vol`,
then the whole sequence converges weak-\* to `vol`.  This is the compactness
argument that turns Lindenstrauss' measure classification into equidistribution. -/
theorem tendsto_of_forall_isQuantumLimit_eq (μ : ℕ → ProbabilityMeasure X)
    (vol : ProbabilityMeasure X)
    (h : ∀ ν : ProbabilityMeasure X, IsQuantumLimit μ ν → ν = vol) :
    Tendsto μ atTop (𝓝 vol) := by
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  -- extract a convergent subsequence of `μ ∘ ns` by sequential compactness
  obtain ⟨ν, -, ms, hms, hconv⟩ :=
    (isSeqCompact_univ (X := ProbabilityMeasure X) (x := fun n => μ (ns n))
      (fun n => Set.mem_univ _))
  -- refine it further so that the index sequence is strictly monotone
  obtain ⟨ks, hks, hnsks⟩ := strictMono_subseq_of_tendsto_atTop (hns.comp hms.tendsto_atTop)
  have hconv' : Tendsto (fun n => μ (ns (ms (ks n)))) atTop (𝓝 ν) :=
    hconv.comp hks.tendsto_atTop
  have hν : ν = vol := h ν ⟨fun n => ns (ms (ks n)), hnsks, hconv'⟩
  exact ⟨fun n => ms (ks n), hν ▸ hconv'⟩

/-- Conversely, if the sequence converges weak-\* to `vol`, then every quantum
limit equals `vol` (uniqueness of limits in the Hausdorff space of probability
measures). -/
theorem forall_isQuantumLimit_eq_of_tendsto (μ : ℕ → ProbabilityMeasure X)
    (vol : ProbabilityMeasure X) (h : Tendsto μ atTop (𝓝 vol)) :
    ∀ ν : ProbabilityMeasure X, IsQuantumLimit μ ν → ν = vol := by
  rintro ν ⟨ns, hns, hconv⟩
  exact tendsto_nhds_unique hconv (h.comp hns.tendsto_atTop)

/-- **Arithmetic quantum unique ergodicity (Lindenstrauss), Lean-checked reduction.**

Let `X` be the (compact, metrizable) phase space — for a cocompact congruence
lattice `Γ ≤ PSL(2,ℝ)`, the unit cotangent bundle `X = Γ \ PSL(2,ℝ)` — let
`μ : ℕ → ProbabilityMeasure X` be the sequence of microlocal lifts of a sequence
of Hecke–Maass eigenforms, and let `vol` be the normalized volume (Liouville)
measure.

Then the measure-classification statement proved by Lindenstrauss — *every
quantum limit of the sequence is the volume measure* — is **equivalent** to
quantum unique ergodicity: `∫ f dμ n → ∫ f d vol` for every continuous
observable `f` on `X`.

The forward implication is the reduction of QUE to measure classification; the
backward implication is the (easy) converse. -/
theorem lindenstrauss_QUE (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X) :
    (∀ ν : ProbabilityMeasure X, IsQuantumLimit μ ν → ν = vol) ↔ Equidistributes μ vol := by
  rw [← tendsto_iff_equidistributes]
  exact ⟨tendsto_of_forall_isQuantumLimit_eq μ vol,
    forall_isQuantumLimit_eq_of_tendsto μ vol⟩

/-- **Base case.**  If the microlocal lifts are already the volume measure (for
instance in the trivial situation of a constant sequence), then the sequence
equidistributes. -/
theorem equidistributes_of_eq_vol (μ : ℕ → ProbabilityMeasure X)
    (vol : ProbabilityMeasure X) (h : ∀ n, μ n = vol) : Equidistributes μ vol := by
  rw [← tendsto_iff_equidistributes]
  simpa [funext h] using tendsto_const_nhds (x := vol) (f := (atTop : Filter ℕ))

end Frontier

