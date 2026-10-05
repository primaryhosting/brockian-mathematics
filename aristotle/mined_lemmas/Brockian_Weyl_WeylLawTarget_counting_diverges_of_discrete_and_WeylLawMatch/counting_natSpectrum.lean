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

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of spectral points `≤ Λ`. -/

theorem counting_natSpectrum (Λ : ℝ) (hΛ : 0 ≤ Λ) : counting natSpectrum Λ = ⌊Λ⌋₊ + 1 := by
  have hset : natSpectrum ∩ Set.Iic Λ = (fun n : ℕ => (n : ℝ)) '' (Set.Iic ⌊Λ⌋₊) := by
    refine Set.Subset.antisymm (natSpectrum_inter_Iic Λ) ?_
    rintro x ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, le_trans (by exact_mod_cast Nat.cast_le.mpr hn) (Nat.floor_le hΛ)⟩
  rw [counting, hset, Set.ncard_image_of_injective _ (fun a b h => by exact_mod_cast h),
    ← Finset.coe_Iic, Set.ncard_coe_finset, Nat.card_Iic]

