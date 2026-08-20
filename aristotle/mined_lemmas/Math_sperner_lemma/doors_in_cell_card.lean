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

/-!
# Sperner's lemma

Every Sperner colouring of a triangulated simplex has an odd number of rainbow cells.
-/

namespace Math

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of cells of `T` containing the face `F`. -/

theorem doors_in_cell_card (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2) :
    ((doors c n).filter (fun F => F ⊆ σ)).card
      = (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card := by
  symm
  apply Finset.card_bij (fun v _ => σ.erase v)
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨?_, Finset.erase_subset _ _⟩
    rw [doors, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, hv.2⟩
    rw [Finset.card_erase_of_mem hv.1, hσ]
    omega
  · intro v hv w hw h
    rw [Finset.mem_filter] at hv hw
    by_contra hne
    have hmem : v ∈ σ.erase w := Finset.mem_erase.2 ⟨hne, hv.1⟩
    rw [← h] at hmem
    exact (Finset.notMem_erase v σ) hmem
  · intro F hF
    rw [Finset.mem_filter, doors, Finset.mem_filter] at hF
    obtain ⟨⟨-, hcard, himg⟩, hsub⟩ := hF
    have hnsub : ¬ σ ⊆ F := by
      intro h
      have := Finset.card_le_card h
      omega
    obtain ⟨v, hvσ, hvF⟩ := Finset.not_subset.1 hnsub
    have hFe : F = σ.erase v := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_erase.2 ⟨fun h => hvF (h ▸ hx), hsub hx⟩
      · rw [Finset.card_erase_of_mem hvσ, hσ, hcard]
        omega
    exact ⟨v, Finset.mem_filter.2 ⟨hvσ, by rw [← hFe, himg]⟩, hFe.symm⟩

omit [Fintype V] in
/-- A rainbow cell has exactly one door. -/
