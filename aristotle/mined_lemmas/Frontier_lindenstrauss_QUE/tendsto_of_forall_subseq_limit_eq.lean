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
open scoped ENNReal NNReal

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

open MeasureTheory Filter Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Weak-\* compactness reduction.**  If every subsequential weak-\* limit of a sequence of
probability measures on a compact metric space equals `vol`, then the whole sequence converges
weak-\* to `vol`. -/

theorem tendsto_of_forall_subseq_limit_eq
    (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (h : ∀ ns : ℕ → ℕ, StrictMono ns → ∀ ν : ProbabilityMeasure X,
      Tendsto (fun k => μ (ns k)) atTop (𝓝 ν) → ν = vol) :
    Tendsto μ atTop (𝓝 vol) := by
  by_contra hcon
  rw [Filter.tendsto_iff_forall_eventually_mem] at hcon
  push_neg at hcon
  obtain ⟨U, hU, hfreq⟩ := hcon
  obtain ⟨ψ, hψ, hψU⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ν, ms, hms, htend⟩ := CompactSpace.tendsto_subseq (fun k => μ (ψ k))
  have hν : ν = vol := h (ψ ∘ ms) (hψ.comp hms) ν htend
  subst hν
  have hev : ∀ᶠ k in atTop, μ (ψ (ms k)) ∈ U := htend hU
  obtain ⟨k, hk⟩ := hev.exists
  exact hψU (ms k) hk

/-- The measure `|f|² · vol`, the natural "quantum probability measure" attached to an
`L²`-normalised (eigen)function `f`. -/
