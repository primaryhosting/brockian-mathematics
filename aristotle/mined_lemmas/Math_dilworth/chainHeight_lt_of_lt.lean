/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
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

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- `chainHeight x` is the largest cardinality of a chain all of whose elements are `≤ x`. -/

lemma chainHeight_lt_of_lt {x y : α} (hxy : x < y) : chainHeight x < chainHeight y := by
  classical
  obtain ⟨s, hchain, hle, hcard⟩ := exists_chain_chainHeight x
  have hy : y ∉ s := by
    intro hy
    exact absurd (hle y hy) (not_le_of_gt hxy)
  set t : Finset α := insert y s with ht
  have htchain : IsChain (· ≤ ·) (t : Set α) := by
    rw [ht, Finset.coe_insert]
    refine hchain.insert ?_
    intro b hb _
    have : b ≤ x := hle b (by simpa using hb)
    exact Or.inr (this.trans hxy.le)
  have htle : ∀ z ∈ t, z ≤ y := by
    intro z hz
    rw [ht, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact le_rfl
    · exact (hle z hz).trans hxy.le
  have hcardt : t.card = s.card + 1 := by
    rw [ht, Finset.card_insert_of_notMem hy]
  have hsup := Finset.le_sup (f := fun s : Finset α =>
      if IsChain (· ≤ ·) (s : Set α) ∧ ∀ z ∈ s, z ≤ y then s.card else 0)
    (Finset.mem_univ t)
  simp only [] at hsup
  rw [if_pos (⟨htchain, htle⟩ : IsChain (· ≤ ·) (t : Set α) ∧ ∀ z ∈ t, z ≤ y)] at hsup
  have : t.card ≤ chainHeight y := by
    rw [chainHeight]; exact hsup
  omega

/-- Every level set of `chainHeight` is an antichain. -/
