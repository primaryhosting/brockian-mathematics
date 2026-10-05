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
Isolation (Valiant–Vazirani) lemma over `GF(2)`, in the counting form needed for
Toda's theorem.
-/
import Mathlib

namespace CS.Toda

open Finset

/-- Bit vectors of length `m`, as vectors over `GF(2)`. -/
abbrev Vec (m : ℕ) := Fin m → ZMod 2

/-- The standard `GF(2)`-bilinear form. -/

theorem isolation {m : ℕ} (A : Finset (Vec m)) (hA : A.Nonempty) :
    8 * (m+2) * ((univ : Finset (Fin (m+2) × Hsp m)).filter
        (fun p => (A.filter (survives p.2 (p.1 : ℕ))).card = 1)).card
      ≥ Fintype.card (Fin (m+2) × Hsp m) := by
  classical
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
    exists_good_k (a := A.card) (Finset.card_pos.mpr hA)
      (by simpa using Finset.card_le_univ A)
  have hkey := isolation_fixed_k (m := m) (k := k) hk2 A hk3 hk4
  set G := ((univ : Finset (Fin (m+2) × Hsp m)).filter
      (fun p => (A.filter (survives p.2 (p.1 : ℕ))).card = 1)) with hG
  set Gk := ((univ : Finset (Hsp m)).filter
      (fun h => (A.filter (survives h k)).card = 1)) with hGk
  have hsub : Gk.card ≤ G.card := by
    apply Finset.card_le_card_of_injOn (fun h => ((⟨k, by omega⟩ : Fin (m+2)), h))
    · intro h hh
      simp only [hGk, mem_filter, mem_univ, true_and] at hh
      simp only [hG, mem_filter, mem_univ, true_and]
      exact hh
    · intro x _ y _ hxy
      simpa using hxy
  have hcard : Fintype.card (Fin (m+2) × Hsp m) = (m+2) * (2^(m+1))^(m+1) := by
    simp [card_Hsp]
  rw [hcard]
  calc 8 * (m+2) * G.card = (m+2) * (8 * G.card) := by ring
    _ ≥ (m+2) * (8 * Gk.card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsub)
    _ ≥ (m+2) * (2^(m+1))^(m+1) := Nat.mul_le_mul_left _ hkey

end CS.Toda

