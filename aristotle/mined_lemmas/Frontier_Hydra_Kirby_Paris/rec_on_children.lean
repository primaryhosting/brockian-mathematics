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

theorem rec_on_children {motive : Hydra → Prop}
    (h : ∀ l : List Hydra, (∀ c ∈ l, motive c) → motive (node l)) (H : Hydra) : motive H :=
  Hydra.rec (motive_2 := fun l => ∀ c ∈ l, motive c) (fun l ih => h l ih)
    (fun c hc => absurd hc List.not_mem_nil)
    (fun a t ha ht c hc => by
      rcases List.mem_cons.1 hc with rfl | h'
      · exact ha
      · exact ht c h') H

/-- Cutting off a head which is attached directly to the root: the head simply
disappears and nothing grows back. -/
inductive CutTop : Hydra → Hydra → Prop
  | head (l₁ l₂ : List Hydra) : CutTop (node (l₁ ++ node [] :: l₂)) (node (l₁ ++ l₂))

/-- Cutting off a head at distance at least `2` from the root, at stage `n`.

* `dup`: the head is at distance exactly `2`; its parent is a child `node (m₁ ++ node [] :: m₂)`
  of the root.  The head is removed, and the resulting subtree `node (m₁ ++ m₂)` is
  reproduced, so that `n + 1` copies of it now hang from the root (i.e. `n` new copies
  grow back).
* `deep`: the head is at distance at least `3` from the root, so the whole modification
  (including the reproduction, which happens at the grandparent of the head) takes place
  inside one of the children of the root. -/
inductive CutDeep (n : ℕ) : Hydra → Hydra → Prop
  | dup (l₁ l₂ m₁ m₂ : List Hydra) :
      CutDeep n (node (l₁ ++ node (m₁ ++ node [] :: m₂) :: l₂))
        (node (l₁ ++ List.replicate (n + 1) (node (m₁ ++ m₂)) ++ l₂))
  | deep (l₁ l₂ : List Hydra) (c c' : Hydra) : CutDeep n c c' →
      CutDeep n (node (l₁ ++ c :: l₂)) (node (l₁ ++ c' :: l₂))

/-- A legal move of the Kirby–Paris hydra game at stage `n`: the player cuts off one
head, and the hydra grows back `n` new copies of the subtree hanging from the grandparent
branch of the cut head (nothing grows back if the head was attached to the root). -/
