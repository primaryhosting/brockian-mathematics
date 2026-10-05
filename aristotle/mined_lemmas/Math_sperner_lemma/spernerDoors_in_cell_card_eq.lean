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

lemma spernerDoors_in_cell_card_eq {J : Finset (Fin (n + 1))} {i₀ : Fin (n + 1)}
    {σ : Finset V} (hσ : σ ∈ spernerCells carrier T J) :
    ((spernerDoors carrier T c J i₀).filter (fun τ => τ ⊆ σ)).card
      = (σ.filter (fun v => (σ.erase v).image c = J.erase i₀)).card := by
  classical
  obtain ⟨hσT, hσcard, hσcar⟩ := Finset.mem_filter.mp hσ
  have hset : (spernerDoors carrier T c J i₀).filter (fun τ => τ ⊆ σ)
      = (σ.filter (fun v => (σ.erase v).image c = J.erase i₀)).image (fun v => σ.erase v) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_image, spernerDoors]
    constructor
    · rintro ⟨⟨hτT, hτcard, hτcar, hτimg⟩, hτσ⟩
      have hcards : τ.card + 1 = σ.card := by omega
      have hss : τ ⊂ σ := Finset.ssubset_iff_of_subset hτσ |>.mpr (by
        by_contra hcon
        push_neg at hcon
        have : σ ⊆ τ := fun x hx => by
          by_contra hxt
          exact hxt (hcon x hx)
        have := Finset.card_le_card this
        omega)
      obtain ⟨v, hvσ, hvτ⟩ := Finset.exists_of_ssubset hss
      have hτe : τ = σ.erase v := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hvτ hx, hτσ hx⟩
        · rw [Finset.card_erase_of_mem hvσ]; omega
      exact ⟨v, ⟨hvσ, by rw [← hτe]; exact hτimg⟩, hτe.symm⟩
    · rintro ⟨v, ⟨hvσ, hvimg⟩, rfl⟩
      refine ⟨⟨hdown σ hσT _ (Finset.erase_subset v σ), ?_, ?_, hvimg⟩,
        Finset.erase_subset v σ⟩
      · rw [Finset.card_erase_of_mem hvσ, ← hσcard]
        have := Finset.card_pos.mpr ⟨v, hvσ⟩
        omega
      · intro w hw; exact hσcar w (Finset.mem_of_mem_erase hw)
  rw [hset]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
  by_contra hne
  have hab' : σ.erase a = σ.erase b := hab
  have hmem : a ∈ σ.erase b := Finset.mem_erase.mpr ⟨hne, ha.1⟩
  rw [← hab'] at hmem
  exact (Finset.notMem_erase a σ) hmem

include hdown hc in
/-- For a cell of `F J`, the number of doors it contains is `1` if the cell is rainbow and
even otherwise. -/
