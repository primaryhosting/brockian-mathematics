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

theorem sperner_lemma (c : V → ℕ) (car : V → Finset ℕ) (n : ℕ) (T : Finset (Finset V))
    (h : IsSpernerTriangulation c car n T) : Odd (rainbowCells c n T).card := by
  induction n generalizing T with
  | zero =>
      obtain ⟨v, rfl, hv⟩ := h
      have : rainbowCells c 0 ({{v}} : Finset (Finset V)) = {{v}} := by
        unfold rainbowCells
        rw [Finset.filter_eq_self]
        intro σ hσ
        rw [Finset.mem_singleton] at hσ
        subst hσ
        simp [hv, Finset.range_one]
      rw [this]
      simp
  | succ n ih =>
      obtain ⟨hcard, hcol, hbd, hrec⟩ := h
      have hIH : Odd (rainbowCells c n (bdry car n T)).card := ih _ hrec
      rw [rainbowCells_bdry c car n T hcol hbd] at hIH
      have hcol' : ∀ σ ∈ T, ∀ v ∈ σ, c v < n + 2 := by
        intro σ hσ v hv
        have := (hcol σ hσ v hv).2 (hcol σ hσ v hv).1
        simpa using this
      have hpar := rainbow_card_eq_oddDoors_card c n T hcard hcol'
      have hmod : (rainbowCells c (n + 1) T).card ≡ (oddDoors c n T).card [MOD 2] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).1 hpar
      rw [Nat.odd_iff] at hIH ⊢
      rw [Nat.ModEq] at hmod
      omega

/-!
### Sanity checks

The notion of a Sperner triangulation used above is not vacuous: it is satisfied both by
genuinely subdivided triangulations and, in every dimension, by the undivided simplex.
-/

/-- The `k`-dimensional face of the standard simplex, inside `Fin (N+1)`. -/
