import Mathlib
/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
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

/-- A comparison-based decision tree sorting 4 elements.

An input is modelled by a permutation `σ : Equiv.Perm (Fin 4)`, where `σ i` is the rank
of the `i`-th input element (so all inputs are distinct and every ranking occurs).
An internal node `node i j l r` performs the single comparison `σ i ≤ σ j`, i.e. it asks
whether the `i`-th element is smaller than the `j`-th element, and branches accordingly.
A leaf outputs a permutation, the algorithm's claimed ranking of the input. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree

/-- The output of the decision tree on the input with ranking `σ`. -/

theorem card_outputs_le (t : DTree) :
    (Finset.univ.image (run t)).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p =>
      simp only [run, depth, pow_zero]
      rw [Finset.image_const Finset.univ_nonempty]
      simp
  | node i j l r ihl ihr =>
      have hsub : Finset.univ.image (run (DTree.node i j l r)) ⊆
          Finset.univ.image (run l) ∪ Finset.univ.image (run r) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨σ, hσ⟩ := hx
        by_cases h : σ i ≤ σ j
        · refine Finset.mem_union_left _ ?_
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨σ, by rw [← hσ]; simp [run, h]⟩
        · refine Finset.mem_union_right _ ?_
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨σ, by rw [← hσ]; simp [run, h]⟩
      calc (Finset.univ.image (run (DTree.node i j l r))).card
          ≤ (Finset.univ.image (run l) ∪ Finset.univ.image (run r)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.image (run l)).card + (Finset.univ.image (run r)).card :=
            Finset.card_union_le _ _
        _ ≤ 2 ^ depth l + 2 ^ depth r := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
              (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        _ = 2 ^ depth (DTree.node i j l r) := by
            rw [depth, pow_add]
            ring

/-- A correct comparison sort of 4 elements must have at least `4! = 24` distinct outputs,
hence `2 ^ depth ≥ 24`. -/
