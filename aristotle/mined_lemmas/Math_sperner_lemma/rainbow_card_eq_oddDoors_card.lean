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

theorem rainbow_card_eq_oddDoors_card (c : V → ℕ) (n : ℕ) (T : Finset (Finset V))
    (hσ : ∀ σ ∈ T, σ.card = n + 2) (hcol : ∀ σ ∈ T, ∀ v ∈ σ, c v < n + 2) :
    ((rainbowCells c (n + 1) T).card : ZMod 2) = ((oddDoors c n T).card : ZMod 2) := by
  -- double counting the incidences between cells and the doors they contain
  have key : ∑ σ ∈ T, (((doors c n).filter (fun F => F ⊆ σ)).card)
      = ∑ F ∈ doors c n, ((T.filter (fun σ => F ⊆ σ)).card) := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hL : ((∑ σ ∈ T, (((doors c n).filter (fun F => F ⊆ σ)).card) : ℕ) : ZMod 2)
      = ((rainbowCells c (n + 1) T).card : ZMod 2) := by
    rw [Nat.cast_sum]
    have hterm : ∀ σ ∈ T, (((((doors c n).filter (fun F => F ⊆ σ)).card) : ℕ) : ZMod 2)
        = if σ.image c = Finset.range (n + 2) then 1 else 0 := by
      intro τ hτ
      rw [cast_zmod_two]
      by_cases h : τ.image c = Finset.range (n + 2)
      · rw [if_pos ((odd_doors_in_cell c n τ (hσ τ hτ) (hcol τ hτ)).2 h), if_pos h]
      · rw [if_neg (fun hh => h ((odd_doors_in_cell c n τ (hσ τ hτ) (hcol τ hτ)).1 hh)), if_neg h]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    simp [rainbowCells]
  have hR : ((∑ F ∈ doors c n, ((T.filter (fun σ => F ⊆ σ)).card) : ℕ) : ZMod 2)
      = ((oddDoors c n T).card : ZMod 2) := by
    rw [Nat.cast_sum]
    have hterm : ∀ F ∈ doors c n, ((((T.filter (fun σ => F ⊆ σ)).card) : ℕ) : ZMod 2)
        = if Odd (cellMult T F) then 1 else 0 := fun F _ => cast_zmod_two _
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    simp [oddDoors]
  rw [← hL, key, hR]

/-- The rainbow cells of the induced boundary triangulation are exactly the odd doors. -/
