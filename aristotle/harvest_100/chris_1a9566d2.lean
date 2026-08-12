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

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The spectral counting function of a set `S ⊆ ℝ` of eigenvalues:
`spectralCounting S T` is the number of elements of `S` that are `≤ T`. -/
noncomputable def spectralCounting (S : Set ℝ) (T : ℝ) : ℕ := (S ∩ Set.Iic T).ncard

/-- `S` has *discrete* spectrum (below every level): only finitely many eigenvalues
lie below any given threshold. -/
def DiscreteSpectrum (S : Set ℝ) : Prop := ∀ T : ℝ, (S ∩ Set.Iic T).Finite

/-- The *Riemann–von Mangoldt* (RVM) condition used here: the spectrum contains
infinitely many points. -/
def RVM (S : Set ℝ) : Prop := S.Infinite

/-- The counting function is monotone in the threshold. -/
theorem spectralCounting_mono {S : Set ℝ} (hdisc : DiscreteSpectrum S) :
    Monotone (spectralCounting S) := by
  intro T₁ T₂ hT
  exact Set.ncard_le_ncard (inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hT)) (hdisc T₂)

/-- If the spectrum below any level is finite and the spectrum is infinite, then for
every `n` there is a level beyond which the counting function is at least `n`. -/
theorem exists_level_le_spectralCounting {S : Set ℝ} (hdisc : DiscreteSpectrum S)
    (hrvm : RVM S) (n : ℕ) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → n ≤ spectralCounting S T := by
  obtain ⟨F, hFS, hFcard⟩ := hrvm.exists_subset_card_eq n
  obtain ⟨M, hM⟩ := F.exists_le
  refine ⟨M, fun T hT => ?_⟩
  have hsub : (F : Set ℝ) ⊆ S ∩ Set.Iic T := fun x hx => ⟨hFS hx, le_trans (hM x hx) hT⟩
  calc n = ((F : Set ℝ)).ncard := by rw [Set.ncard_coe_finset, hFcard]
    _ ≤ (S ∩ Set.Iic T).ncard := Set.ncard_le_ncard hsub (hdisc T)

/-- **Weyl-law target (open discharge).** If the spectrum `S` is discrete (finitely many
eigenvalues below any level) and satisfies the RVM condition (infinitely many
eigenvalues), then the spectral counting function diverges to `+∞`. -/
theorem counting_diverges_of_discrete_and_rvm {S : Set ℝ} (discrete : DiscreteSpectrum S)
    (rvm : RVM S) : Tendsto (spectralCounting S) atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun n =>
    exists_level_le_spectralCounting discrete rvm n

/-- Sanity check: the hypotheses are satisfiable, e.g. by the spectrum `{0, 1, 2, …}`. -/
example : DiscreteSpectrum (Set.range (fun n : ℕ => (n : ℝ))) ∧
    RVM (Set.range (fun n : ℕ => (n : ℝ))) := by
  constructor
  · intro T
    apply Set.Finite.subset ((Set.finite_Icc (0 : ℕ) ⌊T⌋₊).image (fun n : ℕ => (n : ℝ)))
    rintro x ⟨⟨n, rfl⟩, hx⟩
    exact ⟨n, ⟨Nat.zero_le _, Nat.le_floor hx⟩, rfl⟩
  · exact Set.infinite_range_of_injective (fun a b h => by exact_mod_cast h)

end Brockian.Weyl.WeylLawTarget

