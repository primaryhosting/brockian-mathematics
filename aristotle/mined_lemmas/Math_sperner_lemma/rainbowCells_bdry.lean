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

theorem rainbowCells_bdry (c : V → ℕ) (car : V → Finset ℕ) (n : ℕ) (T : Finset (Finset V))
    (hcol : ∀ σ ∈ T, ∀ v ∈ σ, c v ∈ car v ∧ car v ⊆ Finset.range (n + 2))
    (hbd : ∀ F : Finset V, (∃ σ ∈ T, F ⊆ σ) → F.card = n + 1 → Odd (cellMult T F) →
        ∃ i < n + 2, ∀ v ∈ F, i ∉ car v) :
    rainbowCells c n (bdry car n T) = oddDoors c n T := by
  ext F
  simp only [rainbowCells, bdry, oddDoors, doors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hcard, _, hodd⟩, himg⟩
    exact ⟨⟨hcard, himg⟩, hodd⟩
  · rintro ⟨⟨hcard, himg⟩, hodd⟩
    -- `F` lies in some cell
    have hne : (T.filter (fun σ => F ⊆ σ)).Nonempty := by
      rw [← Finset.card_pos]
      have : cellMult T F ≠ 0 := by
        intro h
        rw [Nat.odd_iff, h] at hodd
        exact absurd hodd (by norm_num)
      exact Nat.pos_of_ne_zero this
    obtain ⟨σ, hσ⟩ := hne
    rw [Finset.mem_filter] at hσ
    obtain ⟨i, hi, hcar⟩ := hbd F ⟨σ, hσ.1, hσ.2⟩ hcard hodd
    -- the missing colour must be `n+1`
    have hin : i = n + 1 := by
      by_contra hne'
      have hi' : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
      rw [← himg, Finset.mem_image] at hi'
      obtain ⟨v, hv, hcv⟩ := hi'
      exact hcar v hv (hcv ▸ (hcol σ hσ.1 v (hσ.2 hv)).1)
    refine ⟨⟨hcard, ?_, hodd⟩, himg⟩
    intro v hv j hj
    have h1 : j ∈ Finset.range (n + 2) := (hcol σ hσ.1 v (hσ.2 hv)).2 hj
    have h2 : j ≠ n + 1 := by
      rintro rfl
      exact hcar v hv (hin ▸ hj)
    rw [Finset.mem_range] at h1 ⊢
    omega

/-- **Sperner's lemma**: every Sperner colouring of a triangulated `n`-simplex has an odd
number of rainbow cells. -/
