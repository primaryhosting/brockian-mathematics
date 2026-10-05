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

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u v

/-- A deterministic two-party communication protocol: a binary tree whose internal nodes
are labelled either by a bit that Alice sends (a function of her input `x : X`) or by a bit
that Bob sends (a function of his input `y : Y`), and whose leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number
of bits exchanged. -/

theorem card_image_transcript_le : ∀ (p : Protocol X Y) (A : Finset (X × Y)),
    (A.image fun z => p.transcript z.1 z.2).card ≤ 2 ^ p.cost := by
  intro p
  induction p with
  | leaf b =>
      intro A
      have hsub : (A.image fun z => (leaf b : Protocol X Y).transcript z.1 z.2) ⊆ {[]} := by
        intro t ht
        simp only [Finset.mem_image] at ht
        obtain ⟨z, _, rfl⟩ := ht
        simp [transcript]
      have := Finset.card_le_card hsub
      simpa [cost] using this
  | alice f p q ihp ihq =>
      intro A
      have hsub : (A.image fun z => (alice f p q).transcript z.1 z.2) ⊆
          ((A.image fun z => p.transcript z.1 z.2).image (List.cons true)) ∪
          ((A.image fun z => q.transcript z.1 z.2).image (List.cons false)) := by
        intro t ht
        simp only [Finset.mem_image] at ht
        obtain ⟨z, hz, rfl⟩ := ht
        by_cases hb : f z.1 = true
        · simp only [transcript, hb, if_true, Finset.mem_union, Finset.mem_image]
          exact Or.inl ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        · simp only [transcript, hb, if_false, Finset.mem_union, Finset.mem_image,
            Bool.false_eq_true]
          exact Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 : (2:ℕ) ^ p.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2:ℕ) ^ q.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hu := Finset.card_le_card hsub
      have hunion := Finset.card_union_le
        ((A.image fun z => p.transcript z.1 z.2).image (List.cons true))
        ((A.image fun z => q.transcript z.1 z.2).image (List.cons false))
      have hip : (((A.image fun z => p.transcript z.1 z.2).image (List.cons true))).card
          ≤ (A.image fun z => p.transcript z.1 z.2).card := Finset.card_image_le
      have hiq : (((A.image fun z => q.transcript z.1 z.2).image (List.cons false))).card
          ≤ (A.image fun z => q.transcript z.1 z.2).card := Finset.card_image_le
      have hp := ihp A
      have hq := ihq A
      have hcost : (alice f p q).cost = max p.cost q.cost + 1 := rfl
      rw [hcost, pow_succ]
      omega
  | bob f p q ihp ihq =>
      intro A
      have hsub : (A.image fun z => (bob f p q).transcript z.1 z.2) ⊆
          ((A.image fun z => p.transcript z.1 z.2).image (List.cons true)) ∪
          ((A.image fun z => q.transcript z.1 z.2).image (List.cons false)) := by
        intro t ht
        simp only [Finset.mem_image] at ht
        obtain ⟨z, hz, rfl⟩ := ht
        by_cases hb : f z.2 = true
        · simp only [transcript, hb, if_true, Finset.mem_union, Finset.mem_image]
          exact Or.inl ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        · simp only [transcript, hb, if_false, Finset.mem_union, Finset.mem_image,
            Bool.false_eq_true]
          exact Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 : (2:ℕ) ^ p.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2:ℕ) ^ q.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hu := Finset.card_le_card hsub
      have hunion := Finset.card_union_le
        ((A.image fun z => p.transcript z.1 z.2).image (List.cons true))
        ((A.image fun z => q.transcript z.1 z.2).image (List.cons false))
      have hip : (((A.image fun z => p.transcript z.1 z.2).image (List.cons true))).card
          ≤ (A.image fun z => p.transcript z.1 z.2).card := Finset.card_image_le
      have hiq : (((A.image fun z => q.transcript z.1 z.2).image (List.cons false))).card
          ≤ (A.image fun z => q.transcript z.1 z.2).card := Finset.card_image_le
      have hp := ihp A
      have hq := ihq A
      have hcost : (bob f p q).cost = max p.cost q.cost + 1 := rfl
      rw [hcost, pow_succ]
      omega

end Protocol

/-- The set-disjointness function on subsets of an `n`-element ground set. -/
