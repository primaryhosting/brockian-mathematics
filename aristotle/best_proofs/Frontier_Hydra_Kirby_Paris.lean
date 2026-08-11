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
def children : Hydra → List Hydra
  | node l => l

@[simp] theorem children_node (l : List Hydra) : (node l).children = l := rfl

/-- Induction principle for hydras: to prove a statement for all hydras it suffices to
prove it for `node l` assuming it for all members of `l`. -/
@[elab_as_elim]
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
def Move (n : ℕ) (H H' : Hydra) : Prop := CutTop H H' ∨ CutDeep n H H'

/-- The dead hydra, consisting of the root alone. -/
def dead : Hydra := node []

/-- `H'` is reachable from `H` by a single legal move (at some stage). -/
def MoveRel (H' H : Hydra) : Prop := ∃ n, Move n H H'

/-! ### Basic facts about moves -/

theorem cutTop_moveRel {H H' : Hydra} (h : CutTop H H') : MoveRel H' H := ⟨0, Or.inl h⟩

theorem cutDeep_moveRel {n : ℕ} {H H' : Hydra} (h : CutDeep n H H') : MoveRel H' H :=
  ⟨n, Or.inr h⟩

/-- A hydra which is not dead admits a legal move at every stage. -/
theorem exists_move (n : ℕ) : ∀ {H : Hydra}, H ≠ dead → ∃ H', Move n H H' := by
  intro H
  induction H using rec_on_children with
  | _ l ih =>
    intro hne
    match l, ih with
    | [], _ => exact absurd rfl hne
    | c :: l₂, ih =>
      by_cases hc : c = dead
      · subst hc
        exact ⟨node ([] ++ l₂), Or.inl (CutTop.head [] l₂)⟩
      · obtain ⟨c', hc'⟩ := ih c List.mem_cons_self hc
        rcases hc' with hc' | hc'
        · cases hc' with
          | head m₁ m₂ =>
            exact ⟨node ([] ++ List.replicate (n + 1) (node (m₁ ++ m₂)) ++ l₂),
              Or.inr (CutDeep.dup [] l₂ m₁ m₂)⟩
        · exact ⟨node ([] ++ c' :: l₂), Or.inr (CutDeep.deep [] l₂ c c' hc')⟩

/-! ### Irreflexivity -/

theorem cutTop_ne {H H' : Hydra} (h : CutTop H H') : H ≠ H' := by
  cases h with
  | head l₁ l₂ =>
    intro hEq
    have := congrArg (fun H => H.children.length) hEq
    simp at this

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

theorem moveRel_irrefl (H : Hydra) : ¬ MoveRel H H := by
  rintro ⟨n, h | h⟩
  · exact cutTop_ne h rfl
  · exact cutDeep_ne h rfl

instance : Std.Irrefl MoveRel := ⟨moveRel_irrefl⟩

/-! ### A move on a hydra is a `CutExpand` move on its multiset of children -/

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

theorem acc_of_acc_children {s : Multiset Hydra} (hs : Acc (Relation.CutExpand MoveRel) s) :
    ∀ H : Hydra, (H.children : Multiset Hydra) = s → Acc MoveRel H := by
  induction hs with
  | intro s _ ih =>
    intro H hH
    refine Acc.intro _ fun H' hH' => ?_
    exact ih _ (hH ▸ cutExpand_of_moveRel hH') H' rfl

theorem acc_moveRel (H : Hydra) : Acc MoveRel H := by
  induction H using rec_on_children with
  | _ l ih =>
    refine acc_of_acc_children (s := (l : Multiset Hydra)) ?_ _ rfl
    refine Relation.acc_of_singleton fun c hc => Acc.cutExpand (ih c ?_)
    simpa using hc

/-- **Termination of the Kirby–Paris hydra game**: the relation "`H'` is obtained from `H`
by one legal move" is well-founded. -/
theorem wellFounded_moveRel : WellFounded MoveRel := ⟨acc_moveRel⟩

end Hydra

/-- **The Kirby–Paris hydra theorem.**  Every play of the hydra game terminates, whatever
strategy the player follows and whatever the stage numbers are: if `H 0, H 1, H 2, …` is a
sequence of hydras such that `H (k+1)` is obtained from `H k` by a legal move (at stage
`c k`) as long as the hydra is alive, then the hydra is dead at some point. -/
theorem Hydra_Kirby_Paris (H : ℕ → Hydra) (c : ℕ → ℕ)
    (hplay : ∀ k, H k ≠ Hydra.dead → Hydra.Move (c k) (H k) (H (k + 1))) :
    ∃ k, H k = Hydra.dead := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ X : Hydra, Acc Hydra.MoveRel X → ∀ k, H k = X → False := by
    intro X hX
    induction hX with
    | intro X _ ih =>
      intro k hk
      exact ih (H (k + 1)) (hk ▸ ⟨c k, hplay k (hcon k)⟩) (k + 1) rfl
  exact key (H 0) (Hydra.acc_moveRel _) 0 rfl

/-- Sanity check on the definition of a move: cutting the head of the hydra consisting of a
single branch of length two, at stage `3`, leaves `3 + 1 = 4` heads attached to the root. -/
example : Hydra.Move 3 (Hydra.node [Hydra.node [Hydra.node []]])
    (Hydra.node (List.replicate 4 (Hydra.node []))) := by
  have h := Hydra.CutDeep.dup (n := 3) [] [] [] []
  simpa using Or.inr h

end Frontier

