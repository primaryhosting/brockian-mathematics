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
def SpectrumDiscrete (S : Set ℝ) : Prop :=
  ∀ T : ℝ, (S ∩ Set.Iic T).Finite

/-- The Riemann–von Mangoldt style hypothesis on a spectrum `S`: the spectrum reaches
arbitrarily high energies, i.e. it is unbounded above.  This is the content extracted from
a Riemann–von Mangoldt / Weyl asymptotic for the counting function. -/
def RVM (S : Set ℝ) : Prop :=
  ∀ T : ℝ, ∃ s ∈ S, T < s

/-- The spectral counting function `N_S(T) = #{s ∈ S : s ≤ T}`. -/
noncomputable def countingFunction (S : Set ℝ) (T : ℝ) : ℕ :=
  (S ∩ Set.Iic T).ncard

/-- Under discreteness, the counting function is monotone in the threshold. -/
theorem countingFunction_mono {S : Set ℝ} (hdisc : SpectrumDiscrete S) :
    Monotone (countingFunction S) := by
  intro T T' hTT'
  refine Set.ncard_le_ncard ?_ (hdisc T')
  exact Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hTT')

/-- A spectrum satisfying the Riemann–von Mangoldt hypothesis is infinite. -/
theorem infinite_of_rvm {S : Set ℝ} (hrvm : RVM S) : S.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨s, hsS, hs⟩ := hrvm M
  exact absurd (hM hsS) (not_le.mpr hs)

/-- For every `n` there is a threshold at which the counting function is at least `n`. -/
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
theorem counting_diverges_of_discrete_and_rvm {S : Set ℝ}
    (hdisc : SpectrumDiscrete S) (hrvm : RVM S) :
    Filter.Tendsto (countingFunction S) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro b
  obtain ⟨T, hT⟩ := exists_threshold_countingFunction_ge hdisc hrvm b
  exact ⟨T, fun a ha => hT.trans (countingFunction_mono hdisc ha)⟩

/-- The hypotheses are satisfiable: the model spectrum `{0, 1, 2, …}` is discrete. -/
theorem spectrumDiscrete_natCast :
    SpectrumDiscrete (Set.range (fun n : ℕ => (n : ℝ))) := by
  intro T
  refine Set.Finite.subset ((Set.finite_Iic ⌊T⌋₊).image (fun n : ℕ => (n : ℝ))) ?_
  rintro x ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, Nat.le_floor hx, rfl⟩

/-- The hypotheses are satisfiable: the model spectrum `{0, 1, 2, …}` satisfies RVM. -/
theorem rvm_natCast : RVM (Set.range (fun n : ℕ => (n : ℝ))) := by
  intro T
  obtain ⟨n, hn⟩ := exists_nat_gt T
  exact ⟨(n : ℝ), ⟨n, rfl⟩, hn⟩

/-- Non-vacuity check for the target theorem. -/
example : Filter.Tendsto (countingFunction (Set.range (fun n : ℕ => (n : ℝ))))
    Filter.atTop Filter.atTop :=
  counting_diverges_of_discrete_and_rvm spectrumDiscrete_natCast rvm_natCast

end Brockian.Weyl.WeylLawTarget

