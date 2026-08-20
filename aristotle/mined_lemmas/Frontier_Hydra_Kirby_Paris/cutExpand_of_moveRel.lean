import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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

namespace Frontier

/-- A *hydra* is a finite rooted tree: `node l` is the hydra whose root has the
subtrees in the list `l` hanging from it.  (The order of the children is irrelevant
to the game; it is only a bookkeeping device here.)  The *heads* of a hydra are its
leaves, i.e. the occurrences of `node []`. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The list of subtrees hanging from the root. -/

theorem cutExpand_of_moveRel {H H' : Hydra} (h : MoveRel H' H) :
    Relation.CutExpand MoveRel (H'.children : Multiset Hydra) (H.children : Multiset Hydra) := by
  obtain ⟨n, h | h⟩ := h
  · cases h with
    | head l₁ l₂ =>
      refine ⟨0, node [], by simp, ?_⟩
      simp only [children_node, add_zero, ← Multiset.coe_add, ← Multiset.cons_coe,
        ← Multiset.singleton_add]
      abel
  · cases h with
    | dup l₁ l₂ m₁ m₂ =>
      refine ⟨Multiset.replicate (n + 1) (node (m₁ ++ m₂)), node (m₁ ++ node [] :: m₂),
        fun a' ha' => ?_, ?_⟩
      · rw [Multiset.eq_of_mem_replicate ha']
        exact cutTop_moveRel (CutTop.head m₁ m₂)
      · simp only [children_node, ← Multiset.coe_add, ← Multiset.cons_coe,
          ← Multiset.singleton_add, Multiset.coe_replicate]
        abel
    | deep l₁ l₂ c c' hcc' =>
      refine ⟨{c'}, c, fun a' ha' => ?_, ?_⟩
      · rw [Multiset.mem_singleton.1 ha']
        exact cutDeep_moveRel hcc'
      · simp only [children_node, ← Multiset.coe_add, ← Multiset.cons_coe,
          ← Multiset.singleton_add]
        abel

/-! ### Well-foundedness -/

