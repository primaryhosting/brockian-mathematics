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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`countingFunction S lam` is the number of points of `S` that are `≤ lam`
(counted without multiplicity). -/

theorem card_le_countingFunction {S : Set ℝ} (hlf : ∀ lam : ℝ, (S ∩ Set.Iic lam).Finite)
    {T : Finset ℝ} (hTS : (T : Set ℝ) ⊆ S) {lam : ℝ} (hlam : ∀ x ∈ T, x ≤ lam) :
    T.card ≤ countingFunction S lam := by
  have hsub : (T : Set ℝ) ⊆ S ∩ Set.Iic lam := fun x hx =>
    ⟨hTS hx, hlam x (by simpa using hx)⟩
  have h := Set.ncard_le_ncard hsub (hlf lam)
  simpa [countingFunction, Set.ncard_coe_finset] using h

/-- **Weyl-law counting divergence.**  If the spectrum `S` is locally finite (every lower
section `S ∩ (-∞, lam]` is finite) and there exist infinitely many spectral points, then the
counting function `lam ↦ #(S ∩ (-∞, lam])` diverges to `+∞`. -/
