/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

lemma exists_double_fibre (B : Finset ℕ) (m : ℕ → ℕ) (hpos : ∀ b ∈ B, 1 ≤ m b)
    (hsum : ∑ b ∈ B, m b = B.card + 1) :
    ∃ b0 ∈ B, m b0 = 2 ∧ ∀ b ∈ B, b ≠ b0 → m b = 1 := by
  have hex : ∃ b0 ∈ B, 2 ≤ m b0 := by
    by_contra h
    push_neg at h
    have heq : ∀ b ∈ B, m b = 1 := fun b hb => le_antisymm (by have := h b hb; omega) (hpos b hb)
    rw [Finset.sum_congr rfl heq] at hsum
    simp at hsum
  obtain ⟨b0, hb0, hb0two⟩ := hex
  have hsplit : m b0 + ∑ b ∈ B.erase b0, m b = B.card + 1 := by
    rw [← hsum, Finset.add_sum_erase _ _ hb0]
  have hge : (B.erase b0).card ≤ ∑ b ∈ B.erase b0, m b := by
    calc (B.erase b0).card = ∑ _b ∈ B.erase b0, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun b hb => hpos b (Finset.mem_of_mem_erase hb))
  have hBcard : (B.erase b0).card = B.card - 1 := Finset.card_erase_of_mem hb0
  have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨b0, hb0⟩
  have hm0 : m b0 = 2 := by omega
  refine ⟨b0, hb0, hm0, ?_⟩
  intro b hb hne
  have hb' : b ∈ B.erase b0 := Finset.mem_erase.mpr ⟨hne, hb⟩
  have hsplit2 : m b + ∑ x ∈ (B.erase b0).erase b, m x = ∑ x ∈ B.erase b0, m x :=
    Finset.add_sum_erase _ _ hb'
  have hge2 : ((B.erase b0).erase b).card ≤ ∑ x ∈ (B.erase b0).erase b, m x := by
    calc ((B.erase b0).erase b).card = ∑ _x ∈ (B.erase b0).erase b, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum
      (fun x hx => hpos x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
  have hb2 : 2 ≤ B.card := by
    have : 1 ≤ (B.erase b0).card := Finset.card_pos.mpr ⟨b, hb'⟩
    omega
  have h2 : ((B.erase b0).erase b).card = B.card - 2 := by
    rw [Finset.card_erase_of_mem hb', hBcard]; omega
  have hbpos := hpos b hb
  omega

/-- Counting, modulo 2, the codimension-one faces of a cell `s` whose colours are exactly
`B = A.erase a`: there is exactly one if `s` is rainbow, and an even number otherwise. -/
