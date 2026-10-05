import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma spernerDoors_in_cell_card {J : Finset (Fin (n + 1))} {i₀ : Fin (n + 1)} (hi₀ : i₀ ∈ J)
    {σ : Finset V} (hσ : σ ∈ spernerCells carrier T J) :
    (((spernerDoors carrier T c J i₀).filter (fun τ => τ ⊆ σ)).card : ZMod 2)
      = if σ.image c = J then 1 else 0 := by
  classical
  obtain ⟨hσT, hσcard, hσcar⟩ := Finset.mem_filter.mp hσ
  rw [spernerDoors_in_cell_card_eq carrier T c hdown hσ]
  by_cases hrb : σ.image c = J
  · rw [if_pos hrb, erase_image_filter_card_of_image_eq σ c J i₀ hi₀ hσcard hrb]
    norm_num
  · rw [if_neg hrb]
    obtain ⟨m, hm⟩ := erase_image_filter_card_even σ c J i₀ hi₀ hσcard
      (spernerCells_image_subset carrier T c hc hσ) hrb
    rw [hm]
    push_cast
    ring_nf
    rw [show ((2 : ZMod 2)) = 0 by decide]
    ring

include hpm hc in
/-- For a door of `F J`, the number of cells of `F J` containing it is `1` if the door lies
in the sub-face `J \ {i₀}` (i.e. it is a rainbow cell of that sub-face) and `2` otherwise. -/
