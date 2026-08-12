/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology

namespace Frontier

section QUE

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Sequential compactness of the space of probability measures.**

On a compact metric space `X`, the space of Borel probability measures with the topology of
weak-* convergence is compact and metrizable, hence sequentially compact: every sequence of
probability measures has a weak-* convergent subsequence.

This is the compactness half of the standard quantum-unique-ergodicity argument: the microlocal
lifts of a sequence of eigenfunctions always have weak-* limit points ("quantum limits"). -/
theorem exists_subseq_tendsto_probabilityMeasure (mu : ℕ → ProbabilityMeasure X) :
    ∃ (nu : ProbabilityMeasure X) (ms : ℕ → ℕ), StrictMono ms ∧
      Tendsto (fun n => mu (ms n)) atTop (𝓝 nu) := by
  obtain ⟨nu, -, ms, hms, h⟩ :=
    (isCompact_univ (X := ProbabilityMeasure X)).tendsto_subseq (x := mu)
      (fun n => Set.mem_univ _)
  exact ⟨nu, ms, hms, h⟩

/-- **Arithmetic quantum unique ergodicity: the classification-to-equidistribution reduction.**

Setting: `X` is a compact metric space carrying its Borel σ-algebra — in the arithmetic QUE
situation this is the unit cotangent bundle `Γ \ PSL₂(ℝ)` of a compact congruence surface — and
`vol` is the normalized Liouville (Haar) probability measure on it. The sequence
`mu : ℕ → ProbabilityMeasure X` is the sequence of microlocal lifts of an orthonormal sequence
of Hecke–Maass eigenforms with eigenvalue tending to infinity.

Hypothesis (Lindenstrauss' measure classification input): *every* weak-* limit of a subsequence
of the microlocal lifts is the normalized volume measure — i.e. the only possible quantum limit
is Liouville measure.

Conclusion (quantum unique ergodicity): the whole sequence of microlocal lifts converges weak-*
to the volume measure; equivalently, for every continuous observable `f` on `X`,
`∫ f dmu n → ∫ f dvol`.

The proof is the compactness argument that turns Lindenstrauss' classification of quantum limits
into equidistribution of the full sequence: the space of probability measures on a compact metric
space is compact and metrizable, so a sequence with a unique subsequential limit converges. -/
theorem lindenstrauss_QUE (vol : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (h_quantum_limits : ∀ ns : ℕ → ℕ, StrictMono ns → ∀ nu : ProbabilityMeasure X,
      Tendsto (fun n => mu (ns n)) atTop (𝓝 nu) → nu = vol) :
    Tendsto mu atTop (𝓝 vol) ∧
      ∀ f : C(X, ℝ), Tendsto (fun n => ∫ x, f x ∂(mu n : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(vol : Measure X))) := by
  have key : Tendsto mu atTop (𝓝 vol) := by
    refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
    obtain ⟨nu, ms, hms, hconv⟩ :=
      exists_subseq_tendsto_probabilityMeasure (fun n => mu (ns n))
    have h1 : Tendsto (fun n => ns (ms n)) atTop atTop :=
      hns.comp (StrictMono.tendsto_atTop hms)
    obtain ⟨ks, hks, hstrict⟩ := strictMono_subseq_of_tendsto_atTop h1
    have hconv2 : Tendsto (fun n => mu (ns (ms (ks n)))) atTop (𝓝 nu) :=
      hconv.comp (StrictMono.tendsto_atTop hks)
    have hnu : nu = vol := h_quantum_limits _ hstrict nu hconv2
    exact ⟨fun n => ms (ks n), by simpa [hnu] using hconv2⟩
  refine ⟨key, fun f => ?_⟩
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp key)
    (BoundedContinuousFunction.mkOfCompact f)
  simpa using this

omit [CompactSpace X] in
/-- **Base case of the reduction.** If the microlocal lifts are already the volume measure, the
hypothesis of `Frontier.lindenstrauss_QUE` holds: the constant sequence has `vol` as its unique
subsequential weak-* limit. -/
theorem lindenstrauss_QUE_base (vol : ProbabilityMeasure X) :
    ∀ ns : ℕ → ℕ, StrictMono ns → ∀ nu : ProbabilityMeasure X,
      Tendsto (fun n => (fun _ => vol) (ns n)) atTop (𝓝 nu) → nu = vol := by
  intro ns _ nu hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

/-- Portmanteau consequence of quantum unique ergodicity: under the hypothesis of
`Frontier.lindenstrauss_QUE`, the mass that the microlocal lifts put on an open set `U`
is asymptotically at least `vol U`. -/
theorem lindenstrauss_QUE_le_liminf_open (vol : ProbabilityMeasure X)
    (mu : ℕ → ProbabilityMeasure X)
    (h_quantum_limits : ∀ ns : ℕ → ℕ, StrictMono ns → ∀ nu : ProbabilityMeasure X,
      Tendsto (fun n => mu (ns n)) atTop (𝓝 nu) → nu = vol)
    {U : Set X} (hU : IsOpen U) :
    (vol : Measure X) U ≤ liminf (fun n => (mu n : Measure X) U) atTop :=
  ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (lindenstrauss_QUE vol mu h_quantum_limits).1 hU

end QUE

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

