import Mathlib
/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ENNReal

/-! ## The Hilbert space `ℓ²(ℤ, ℝ)` -/

/-- The Hilbert space `ℓ²(ℤ)` (real scalars) on which the almost Mathieu operator acts. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℝ) 2

/-! ## Multiplication and shift operators on `ℓ²(ℤ)` -/


theorem tenMartini_of_measure_zero
    (h : ∀ lam alpha theta : ℝ, 0 < lam → Irrational alpha →
        alpha ∈ Set.Ioo (0 : ℝ) 1 → theta ∈ Set.Ico (0 : ℝ) 1 →
        (amoSpectrum lam alpha theta).Nonempty ∧
        MeasureTheory.volume (amoSpectrum lam alpha theta) = 0 ∧
        Preperfect (amoSpectrum lam alpha theta)) :
    TenMartini := by
  refine avila_ten_martini.2 fun lam alpha theta hlam hirr hIoo hIco => ?_
  obtain ⟨hne, hvol, hacc⟩ := h lam alpha theta hlam hirr hIoo hIco
  exact ⟨hne, interior_eq_empty_of_volume_eq_zero hvol, hacc⟩

end Frontier

