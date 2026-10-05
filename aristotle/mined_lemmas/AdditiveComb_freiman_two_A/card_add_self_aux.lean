/-
# Freiman Two A
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.freiman_two_A
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace AdditiveComb

open Finset

/-- Auxiliary induction: a nonempty finite set of integers of cardinality `n` has
`|A + A| ≥ 2n - 1`. -/

private lemma card_add_self_aux :
    ∀ n : ℕ, ∀ A : Finset ℤ, A.card = n → A.Nonempty → 2 * n - 1 ≤ (A + A).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hcard hA
    rcases lt_or_ge n 2 with hn | hn
    · have h1 : (0 : ℕ) < (A + A).card := Finset.card_pos.mpr (hA.add hA)
      omega
    · set m := A.max' hA with hm
      have hmA : m ∈ A := A.max'_mem hA
      set A' := A.erase m with hA'
      have hA'card : A'.card = n - 1 := by rw [hA', Finset.card_erase_of_mem hmA, hcard]
      have hA'ne : A'.Nonempty := by
        rw [← Finset.card_pos, hA'card]; omega
      set m' := A'.max' hA'ne with hm'
      have hm'A' : m' ∈ A' := A'.max'_mem hA'ne
      have hm'A : m' ∈ A := Finset.mem_of_mem_erase hm'A'
      have hm'lt : m' < m :=
        lt_of_le_of_ne (A.le_max' m' hm'A) (Finset.ne_of_mem_erase hm'A')
      have hbound : ∀ z ∈ A' + A', z ≤ m' + m' := by
        intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
        exact add_le_add (A'.le_max' a ha) (A'.le_max' b hb)
      have h1 : m + m' ∉ A' + A' := by
        intro h
        have := hbound _ h
        omega
      have h2 : m + m ∉ insert (m + m') (A' + A') := by
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · omega
        · have := hbound _ h
          omega
      have hsub : insert (m + m) (insert (m + m') (A' + A')) ⊆ A + A := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.add_mem_add hmA hmA
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.add_mem_add hmA hm'A
        · exact Finset.add_subset_add (Finset.erase_subset _ _) (Finset.erase_subset _ _) hz
      have hcards := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1] at hcards
      have hrec : 2 * (n - 1) - 1 ≤ (A' + A').card := ih (n - 1) (by omega) A' hA'card hA'ne
      omega

/-- **Basic doubling lower bound.** For a finite nonempty set `A` of integers,
`2 * |A| - 1 ≤ |A + A|`. -/
