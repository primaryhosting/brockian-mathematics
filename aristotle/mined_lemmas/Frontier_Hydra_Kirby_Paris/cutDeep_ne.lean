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

theorem cutDeep_ne {n : ℕ} : ∀ {H H' : Hydra}, CutDeep n H H' → H ≠ H' := by
  intro H H' h
  induction h with
  | dup l₁ l₂ m₁ m₂ =>
    intro hEq
    have hchild := congrArg Hydra.children hEq
    simp only [children_node] at hchild
    have hlen := congrArg List.length hchild
    simp at hlen
    -- the length forces `n = 0`, and then the two subtrees would have to be equal
    have hn : n = 0 := by omega
    subst hn
    simp only [Nat.zero_add, List.replicate_one, List.append_assoc, List.cons_append,
      List.nil_append] at hchild
    have h3 : node (m₁ ++ node [] :: m₂) = node (m₁ ++ m₂) :=
      List.head_eq_of_cons_eq (List.append_cancel_left hchild)
    have h4 := congrArg (fun H => H.children.length) h3
    simp at h4
  | deep l₁ l₂ c c' _ ih =>
    intro hEq
    apply ih
    have := congrArg (fun H => H.children) hEq
    simp only [children_node] at this
    exact List.head_eq_of_cons_eq (List.append_cancel_left this)

