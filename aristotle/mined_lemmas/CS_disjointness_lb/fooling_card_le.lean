/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
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

namespace CS

/-! ## The communication model

A two-party deterministic communication protocol on inputs `X` (Alice) and `Y` (Bob) is a
binary tree.  At an `alice` node the bit sent depends only on Alice's input, at a `bob` node
only on Bob's input, and a `leaf` carries the output of the protocol.  The `cost` of a protocol
is the depth of the tree, i.e. the number of bits exchanged in the worst case. -/
inductive Protocol (X Y : Type) : Type
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- The output of a protocol on a given pair of inputs. -/

lemma fooling_card_le {n : ℕ} (P : Protocol (Inp n) (Inp n)) :
    ∀ A B : Finset (Inp n),
      (∀ x ∈ A, ∀ y ∈ B, P.run x y = true → Disjoint x y) →
      (A.filter (fun S => Sᶜ ∈ B ∧ P.run S Sᶜ = true)).card ≤ 2 ^ P.cost := by
  induction P with
  | leaf b =>
      intro A B hAB
      cases b with
      | false =>
          have : A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.leaf false :
              Protocol (Inp n) (Inp n)).run S Sᶜ = true) = ∅ := by
            apply Finset.filter_false_of_mem
            intro S _
            simp
          rw [this]
          simp
      | true =>
          have hone : ∀ S ∈ A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.leaf true :
              Protocol (Inp n) (Inp n)).run S Sᶜ = true),
              ∀ T ∈ A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.leaf true :
              Protocol (Inp n) (Inp n)).run S Sᶜ = true), S = T := by
            intro S hS T hT
            simp only [Finset.mem_filter] at hS hT
            have h1 : Disjoint S Tᶜ := hAB S hS.1 Tᶜ hT.2.1 rfl
            have h2 : Disjoint T Sᶜ := hAB T hT.1 Sᶜ hS.2.1 rfl
            have := (disjoint_compl_iff_subset S T).mp h1
            have := (disjoint_compl_iff_subset T S).mp h2
            exact Finset.Subset.antisymm ‹S ⊆ T› ‹T ⊆ S›
          have := Finset.card_le_one.mpr hone
          simpa using this
  | alice f p q ihp ihq =>
      intro A B hAB
      set A0 := A.filter (fun S => f S = false) with hA0
      set A1 := A.filter (fun S => f S = true) with hA1
      have hp : (A0.filter (fun S => Sᶜ ∈ B ∧ p.run S Sᶜ = true)).card ≤ 2 ^ p.cost := by
        refine ihp A0 B ?_
        intro x hx y hy hrun
        simp only [hA0, Finset.mem_filter] at hx
        refine hAB x hx.1 y hy ?_
        simp [hx.2, hrun]
      have hq : (A1.filter (fun S => Sᶜ ∈ B ∧ q.run S Sᶜ = true)).card ≤ 2 ^ q.cost := by
        refine ihq A1 B ?_
        intro x hx y hy hrun
        simp only [hA1, Finset.mem_filter] at hx
        refine hAB x hx.1 y hy ?_
        simp [hx.2, hrun]
      have hsplit :
          (A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.alice f p q).run S Sᶜ = true)).card
            = (A0.filter (fun S => Sᶜ ∈ B ∧ p.run S Sᶜ = true)).card
              + (A1.filter (fun S => Sᶜ ∈ B ∧ q.run S Sᶜ = true)).card := by
        rw [hA0, hA1, Finset.filter_filter, Finset.filter_filter]
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext S
          by_cases hf : f S = true <;>
            simp [Finset.mem_filter, Finset.mem_union, hf, Protocol.run]
        · rw [Finset.disjoint_left]
          intro S hS hS'
          simp only [Finset.mem_filter] at hS hS'
          rw [hS.2.1] at hS'
          exact Bool.false_ne_true hS'.2.1
      rw [hsplit]
      calc (A0.filter (fun S => Sᶜ ∈ B ∧ p.run S Sᶜ = true)).card
              + (A1.filter (fun S => Sᶜ ∈ B ∧ q.run S Sᶜ = true)).card
          ≤ 2 ^ p.cost + 2 ^ q.cost := Nat.add_le_add hp hq
        _ ≤ 2 ^ (max p.cost q.cost) + 2 ^ (max p.cost q.cost) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
              (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        _ = 2 ^ (Protocol.alice f p q).cost := by
            rw [Protocol.cost, pow_succ]; ring
  | bob g p q ihp ihq =>
      intro A B hAB
      set B0 := B.filter (fun T => g T = false) with hB0
      set B1 := B.filter (fun T => g T = true) with hB1
      have hp : (A.filter (fun S => Sᶜ ∈ B0 ∧ p.run S Sᶜ = true)).card ≤ 2 ^ p.cost := by
        refine ihp A B0 ?_
        intro x hx y hy hrun
        simp only [hB0, Finset.mem_filter] at hy
        refine hAB x hx y hy.1 ?_
        simp [hy.2, hrun]
      have hq : (A.filter (fun S => Sᶜ ∈ B1 ∧ q.run S Sᶜ = true)).card ≤ 2 ^ q.cost := by
        refine ihq A B1 ?_
        intro x hx y hy hrun
        simp only [hB1, Finset.mem_filter] at hy
        refine hAB x hx y hy.1 ?_
        simp [hy.2, hrun]
      have hsplit :
          (A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.bob g p q).run S Sᶜ = true)).card
            = (A.filter (fun S => Sᶜ ∈ B0 ∧ p.run S Sᶜ = true)).card
              + (A.filter (fun S => Sᶜ ∈ B1 ∧ q.run S Sᶜ = true)).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext S
          by_cases hg : g Sᶜ = true <;>
            simp [hB0, hB1, Finset.mem_filter, Finset.mem_union, hg, Protocol.run]
        · rw [Finset.disjoint_left]
          intro S hS hS'
          simp only [hB0, hB1, Finset.mem_filter] at hS hS'
          rw [hS.2.1.2] at hS'
          exact Bool.false_ne_true hS'.2.1.2
      rw [hsplit]
      calc (A.filter (fun S => Sᶜ ∈ B0 ∧ p.run S Sᶜ = true)).card
              + (A.filter (fun S => Sᶜ ∈ B1 ∧ q.run S Sᶜ = true)).card
          ≤ 2 ^ p.cost + 2 ^ q.cost := Nat.add_le_add hp hq
        _ ≤ 2 ^ (max p.cost q.cost) + 2 ^ (max p.cost q.cost) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
              (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        _ = 2 ^ (Protocol.bob g p q).cost := by
            rw [Protocol.cost, pow_succ]; ring

/-- Specialisation of `fooling_card_le` to the full rectangle: a protocol that accepts only
disjoint pairs accepts at most `2 ^ cost` of the `2 ^ n` fooling-set pairs `(S, Sᶜ)`. -/
