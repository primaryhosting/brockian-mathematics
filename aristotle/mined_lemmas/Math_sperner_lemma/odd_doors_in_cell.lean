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

theorem odd_doors_in_cell (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2)
    (hcol : ∀ v ∈ σ, c v < n + 2) :
    (Odd ((doors c n).filter (fun F => F ⊆ σ)).card ↔ σ.image c = Finset.range (n + 2)) := by
  rw [doors_in_cell_card c n σ hσ]
  constructor
  · intro h
    by_contra hne
    rw [Nat.odd_iff] at h
    rcases nonrainbow_case c n σ hσ hcol hne with h0 | h2 <;> omega
  · intro h
    rw [rainbow_case c n σ hσ h]
    exact odd_one

/-- Double counting: mod 2, the number of rainbow cells equals the number of odd doors. -/
