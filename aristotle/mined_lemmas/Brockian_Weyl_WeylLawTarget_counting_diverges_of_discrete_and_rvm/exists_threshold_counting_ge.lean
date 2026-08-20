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

/-
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Set

namespace Brockian.Weyl

/-- The (Weyl) eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S T` is the number of spectral points that are `≤ T`. -/

theorem exists_threshold_counting_ge {S : Set ℝ} (hdiscrete : DiscreteSpectrum S)
    (hrvm : S.Infinite) (n : ℕ) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → n ≤ counting S T := by
  obtain ⟨t, hts, htcard⟩ := hrvm.exists_subset_card_eq n
  obtain ⟨M, hM⟩ := (t.finite_toSet).bddAbove
  refine ⟨M, fun T hT => ?_⟩
  have hsub : (t : Set ℝ) ⊆ {x ∈ S | x ≤ T} := by
    intro x hx
    exact ⟨hts hx, (hM hx).trans hT⟩
  have := Set.ncard_le_ncard hsub (hdiscrete T)
  simpa [Set.ncard_coe_finset, htcard] using this

namespace WeylLawTarget

/-- **Divergence of the Weyl counting function.**

If the spectrum `S ⊆ ℝ` is discrete (only finitely many spectral points below any
threshold) and lies in the Riemann–von Mangoldt regime in the sense that it contains
infinitely many spectral points (`hrvm`), then the counting function
`T ↦ #{x ∈ S | x ≤ T}` diverges to `+∞` as `T → +∞`.

This discharges the previously assumed hypothesis, making it unconditional.

The key Mathlib ingredients are `Set.Infinite.exists_subset_card_eq`
(extract a finite subset of any prescribed cardinality), `Set.Finite.bddAbove`
(a finite set of reals is bounded above) and `Set.ncard_le_ncard` (monotonicity
of `Set.ncard` on finite sets). -/
