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

set_option grind.warning false

namespace Brockian

/-- `H` is an *admissible* tuple of integers: for every prime `p` there is a residue class
mod `p` which is avoided by every element of `H`. -/

theorem nu_lt_of_admissible {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    nu H p < p := by
  obtain ⟨r, hrp, hr⟩ := hH p hp
  have hsub : ((Finset.range p).filter
      (fun r : ℕ => ∃ x ∈ H, ((p : ℤ) ∣ (x - (r : ℤ))))) ⊂ Finset.range p := by
    refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr ⟨r, ?_, ?_⟩
    · exact Finset.mem_range.mpr hrp
    · simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro _
      push_neg
      intro x hx
      exact hr x hx
  have := Finset.card_lt_card hsub
  simpa [nu] using this

/-- Every local factor of the singular series of an admissible tuple is positive. -/
