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

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of a set `S ⊆ ℝ` (thought of as the spectrum of an
operator, listed without multiplicity): `spectralCounting S t` is the number of spectral
points that are `≤ t`. -/

theorem spectralCounting_natSpectrum {t : ℝ} (ht : 0 ≤ t) :
    spectralCounting natSpectrum t = ⌊t⌋₊ + 1 := by
  have hset : natSpectrum ∩ Set.Iic t = (fun n : ℕ => (n : ℝ)) '' Set.Iic ⌊t⌋₊ := by
    refine Set.Subset.antisymm (natSpectrum_inter_Iic t) ?_
    rintro x ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, by
      simpa using (Nat.cast_le (α := ℝ) |>.mpr hn).trans (Nat.floor_le ht)⟩
  rw [spectralCounting, hset, Set.ncard_image_of_injective _ Nat.cast_injective,
    Set.ncard_Iic_nat]

