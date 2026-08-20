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
noncomputable def counting (S : Set ℝ) (T : ℝ) : ℕ := {x ∈ S | x ≤ T}.ncard

/-- Discreteness of the spectrum, in the form used by the Weyl law: below any
threshold `T` only finitely many spectral points occur. -/
def DiscreteSpectrum (S : Set ℝ) : Prop := ∀ T : ℝ, {x ∈ S | x ≤ T}.Finite

/-- The counting function of a discrete spectrum is monotone. -/
theorem counting_mono {S : Set ℝ} (hS : DiscreteSpectrum S) : Monotone (counting S) := by
  intro T₁ T₂ hT
  refine Set.ncard_le_ncard ?_ (hS T₂)
  rintro x ⟨hxS, hxT⟩
  exact ⟨hxS, hxT.trans hT⟩

/-- If `S` is infinite, then for every `n` there is a threshold beyond which the
counting function is at least `n`. -/
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
theorem counting_diverges_of_discrete_and_rvm {S : Set ℝ}
    (hdiscrete : Brockian.Weyl.DiscreteSpectrum S) (hrvm : S.Infinite) :
    Filter.Tendsto (Brockian.Weyl.counting S) Filter.atTop Filter.atTop := by
  refine tendsto_atTop_atTop.2 fun n => ?_
  obtain ⟨T₀, hT₀⟩ := Brockian.Weyl.exists_threshold_counting_ge hdiscrete hrvm n
  exact ⟨T₀, hT₀⟩

end WeylLawTarget

/-! ### Non-vacuity: the hypotheses are simultaneously satisfiable -/

/-- The spectrum `{0, 1, 2, …} ⊆ ℝ` is discrete. -/
theorem discreteSpectrum_natCast : DiscreteSpectrum (Set.range (fun n : ℕ => (n : ℝ))) := by
  intro T
  apply Set.Finite.subset ((Set.finite_Icc 0 ⌊T⌋₊).image (fun n : ℕ => (n : ℝ)))
  rintro x ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, ⟨Nat.zero_le _, Nat.le_floor hx⟩, rfl⟩

/-- The spectrum `{0, 1, 2, …} ⊆ ℝ` is infinite. -/
theorem infinite_natCast_range : (Set.range (fun n : ℕ => (n : ℝ))).Infinite :=
  Set.infinite_range_of_injective fun a b h => by exact_mod_cast h

/-- Both hypotheses of `counting_diverges_of_discrete_and_rvm` hold for the model
spectrum `{0, 1, 2, …}`, so the theorem is not vacuous. -/
example : Filter.Tendsto (counting (Set.range (fun n : ℕ => (n : ℝ)))) Filter.atTop Filter.atTop :=
  WeylLawTarget.counting_diverges_of_discrete_and_rvm discreteSpectrum_natCast
    infinite_natCast_range

end Brockian.Weyl

