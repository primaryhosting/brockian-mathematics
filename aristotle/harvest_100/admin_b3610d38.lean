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

namespace AdditiveComb

/-- **Basic doubling bound.** For a finite nonempty set `A` of integers,
`2 * |A| - 1 ≤ |A + A|`. -/
theorem freiman_two_A (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by
  classical
  set m := A.min' hA with hm
  set M := A.max' hA with hMdef
  set S1 := A.image (fun a => m + a) with hS1
  set S2 := A.image (fun a => a + M) with hS2
  have hsub : S1 ∪ S2 ⊆ A + A := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
      exact Finset.add_mem_add (A.min'_mem hA) ha
    · rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
      exact Finset.add_mem_add ha (A.max'_mem hA)
  have h1 : S1.card = A.card := Finset.card_image_of_injective _ (add_right_injective m)
  have h2 : S2.card = A.card := Finset.card_image_of_injective _ (add_left_injective M)
  have hinter : S1 ∩ S2 = {m + M} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · refine Finset.mem_inter.2 ⟨?_, ?_⟩
      · exact Finset.mem_image.2 ⟨M, A.max'_mem hA, rfl⟩
      · exact Finset.mem_image.2 ⟨m, A.min'_mem hA, rfl⟩
    · intro x hx
      rcases Finset.mem_inter.1 hx with ⟨hx1, hx2⟩
      rcases Finset.mem_image.1 hx1 with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.1 hx2 with ⟨b, hb, hbx⟩
      have haM : a ≤ M := A.le_max' a ha
      have hmb : m ≤ b := A.min'_le b hb
      have hle : m + a ≤ m + M := by omega
      have hge : m + M ≤ b + M := by omega
      omega
  have hcard : (S1 ∪ S2).card = 2 * A.card - 1 := by
    have := Finset.card_union_add_card_inter S1 S2
    rw [hinter, h1, h2] at this
    simp only [Finset.card_singleton] at this
    omega
  calc 2 * A.card - 1 = (S1 ∪ S2).card := hcard.symm
    _ ≤ (A + A).card := Finset.card_le_card hsub

end AdditiveComb

