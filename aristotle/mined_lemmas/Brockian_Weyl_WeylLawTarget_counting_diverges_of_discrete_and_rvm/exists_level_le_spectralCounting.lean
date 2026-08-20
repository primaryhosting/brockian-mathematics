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
