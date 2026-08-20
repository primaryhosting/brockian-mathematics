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

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian.Weyl.WeylLawTarget

/-- A spectrum `S ⊆ ℝ` is *discrete* (in the Weyl-law sense: discrete and proper, i.e.
locally finite with no accumulation at finite energy) when only finitely many spectral
points lie below any threshold `T`. -/

theorem exists_threshold_countingFunction_ge {S : Set ℝ} (hdisc : SpectrumDiscrete S)
    (hrvm : RVM S) (n : ℕ) : ∃ T : ℝ, n ≤ countingFunction S T := by
  obtain ⟨t, htS, htcard⟩ := (infinite_of_rvm hrvm).exists_subset_card_eq n
  obtain ⟨M, hM⟩ := t.finite_toSet.bddAbove
  refine ⟨M, ?_⟩
  have hsub : (t : Set ℝ) ⊆ S ∩ Set.Iic M := fun x hx => ⟨htS hx, hM hx⟩
  calc (n : ℕ) = (t : Set ℝ).ncard := by rw [Set.ncard_coe_finset, htcard]
    _ ≤ countingFunction S M := Set.ncard_le_ncard hsub (hdisc M)

/-- **Weyl-law target.**  If a spectrum `S ⊆ ℝ` is discrete (only finitely many spectral
points below each threshold) and satisfies the Riemann–von Mangoldt hypothesis (it is
unbounded above), then its counting function diverges: `N_S(T) → ∞` as `T → ∞`.

This is the unconditional form: no extra hypothesis is assumed beyond discreteness and RVM. -/
