/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- below as the module docstring of this file.)

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *hydra* is a finite rooted tree.  A move of the Kirby–Paris hydra game consists of
choosing a *head* (a leaf) and chopping it off:

* if the head is attached to the root, nothing grows back;
* otherwise, let `p` be the parent of the head and `g` the grandparent.  After the head is
  removed, an arbitrary finite number `n` of copies of the (modified) subtree rooted at `p`
  are attached to `g`.

We model hydras by the inductive type `Frontier.Hydra` (a rooted tree with an ordered list of
children — the ordering is immaterial, all statements below are invariant under it), and the
moves by the relation `Frontier.Hydra.Move`.  `Move h h'` means: `h'` arises from `h` by one
legal move of the game, with an arbitrary number of copies grown back (so our result covers
every convention about how many heads regrow at each stage, and any strategy of the player
and of the hydra).

The main results are:

* `Frontier.Hydra.wellFounded_move` : the reversed move relation is well founded;
* `Frontier.Hydra_Kirby_Paris` : there is no infinite play, i.e. every hydra game terminates,
  for every strategy;
* `Frontier.Hydra.strategy_terminates` : iterating any legal strategy from any starting hydra
  reaches the dead hydra in finitely many steps;
* `Frontier.Hydra.exists_move` : the game gets stuck only at the dead hydra.

The termination proof follows the classical argument, in the guise of Mathlib's
`Relation.CutExpand`: we build a well-founded relation `HLT` on hydras (`HLT h' h` holds when
the children of `h'` are obtained from those of `h` by a cut-and-expand step for `HLT` itself),
show that it is well founded, and check that every move of the game strictly decreases it.
-/

namespace Frontier

/-- A hydra: a finite rooted tree.  `node l` is the tree whose root has the children `l`.
`node []` is a single head, the "dead" hydra. -/
inductive Hydra : Type
  | node : List Hydra → Hydra
  deriving Inhabited

namespace Hydra

/-- The dead hydra: a single node with no children. -/
abbrev dead : Hydra := .node []

/-! ### A well-founded relation on hydras -/

/-- `HLT h' h` holds when the multiset of children of `h'` is obtained from the multiset of
children of `h` by removing one child `a` and adding back finitely many hydras, each of which
is `HLT`-smaller than `a`.  This is exactly `Relation.CutExpand HLT` on the children
(see `HLT_iff_cutExpand`). -/
inductive HLT : Hydra → Hydra → Prop
  | mk (l' l : List Hydra) (t : Multiset Hydra) (a : Hydra)
      (ha : ∀ a' ∈ t, HLT a' a)
      (he : (l' : Multiset Hydra) + {a} = (l : Multiset Hydra) + t) :
      HLT (.node l') (.node l)

theorem HLT_iff_cutExpand (l' l : List Hydra) :
    HLT (.node l') (.node l) ↔
      Relation.CutExpand HLT (l' : Multiset Hydra) (l : Multiset Hydra) := by
  constructor
  · rintro ⟨_, _, t, a, ha, he⟩
    exact ⟨t, a, ha, he⟩
  · rintro ⟨t, a, ha, he⟩
    exact .mk l' l t a ha he

/-- `HLT` is irreflexive. -/
theorem HLT.ne : ∀ {x y : Hydra}, HLT x y → x ≠ y := by
  intro x y h
  induction h with
  | mk l' l t a _ he ih =>
    intro heq
    have hnode : l' = l := by injection heq
    subst hnode
    have ht : ({a} : Multiset Hydra) = t := add_left_cancel he
    exact ih a (by rw [← ht]; simp) rfl

instance : Std.Irrefl HLT := ⟨fun _ h => h.ne rfl⟩

private theorem acc_node_of_acc_cutExpand :
    ∀ {s : Multiset Hydra}, Acc (Relation.CutExpand HLT) s →
      ∀ l : List Hydra, (l : Multiset Hydra) = s → Acc HLT (.node l) := by
  intro s hs
  induction hs with
  | intro s _ ih =>
    intro l hl
    refine Acc.intro _ ?_
    rintro y hy
    obtain ⟨l', rfl⟩ : ∃ l', y = .node l' := by cases y with | node l' => exact ⟨l', rfl⟩
    refine ih (l' : Multiset Hydra) ?_ l' rfl
    rw [← hl]
    exact (HLT_iff_cutExpand l' l).1 hy

/-- Every hydra is accessible for `HLT`. -/
theorem HLT.acc (h : Hydra) : Acc HLT h := by
  induction h using Hydra.rec (motive_2 := fun l => ∀ a ∈ l, Acc HLT a) with
  | node l ih =>
    refine acc_node_of_acc_cutExpand (Relation.acc_of_singleton ?_) l rfl
    intro a ha
    exact (ih a (by simpa using ha)).cutExpand
  | nil b hb => exact absurd hb (by simp)
  | cons a l iha ihl b hb =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact iha
    · exact ihl b hb

theorem wellFounded_HLT : WellFounded HLT := ⟨HLT.acc⟩

/-! ### The moves of the Kirby–Paris hydra game -/

/-- One move of the Kirby–Paris hydra game: `Move h h'` means that `h'` is obtained from `h`
by chopping off one head.

* `chopHead` : the head is a child of the root; it is simply removed.
* `dup` : the head is a grandchild of the root; the parent subtree, with the head removed, is
  replaced by `n` copies of itself (`n` arbitrary — this covers every convention on the number
  of heads that grow back).
* `deeper` : a move performed inside one of the subtrees hanging from the root. -/
inductive Move : Hydra → Hydra → Prop
  | chopHead (l₁ l₂ : List Hydra) :
      Move (.node (l₁ ++ .node [] :: l₂)) (.node (l₁ ++ l₂))
  | dup (n : ℕ) (l₁ l₂ r₁ r₂ : List Hydra) :
      Move (.node (l₁ ++ .node (r₁ ++ .node [] :: r₂) :: l₂))
        (.node (l₁ ++ List.replicate n (.node (r₁ ++ r₂)) ++ l₂))
  | deeper (l₁ l₂ : List Hydra) (h h' : Hydra) :
      Move h h' → Move (.node (l₁ ++ h :: l₂)) (.node (l₁ ++ h' :: l₂))

/-- Every move of the game strictly decreases the well-founded relation `HLT`. -/
theorem HLT_of_move {h h' : Hydra} (hm : Move h h') : HLT h' h := by
  induction hm with
  | chopHead l₁ l₂ =>
    refine (HLT_iff_cutExpand _ _).2 ⟨0, .node [], by simp, ?_⟩
    simp only [add_zero, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
    abel
  | dup n l₁ l₂ r₁ r₂ =>
    refine (HLT_iff_cutExpand _ _).2
      ⟨Multiset.replicate n (.node (r₁ ++ r₂)), .node (r₁ ++ .node [] :: r₂), ?_, ?_⟩
    · intro a' ha'
      rw [Multiset.eq_of_mem_replicate ha']
      refine (HLT_iff_cutExpand _ _).2 ⟨0, .node [], by simp, ?_⟩
      simp only [add_zero, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
      abel
    · simp only [← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add,
        ← Multiset.coe_replicate]
      abel
  | deeper l₁ l₂ a b _ ih =>
    refine (HLT_iff_cutExpand _ _).2 ⟨{b}, a, ?_, ?_⟩
    · intro a' ha'
      rw [Multiset.mem_singleton.1 ha']
      exact ih
    · simp only [← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
      abel

/-- The reversed move relation is well founded: the hydra always loses. -/
theorem wellFounded_move : WellFounded (fun h' h => Move h h') :=
  Subrelation.wf HLT_of_move wellFounded_HLT

/-! ### Termination of the game -/

/-- **Kirby–Paris**: every hydra game terminates.  There is no infinite sequence of hydras in
which each term is obtained from the previous one by a legal move; in particular the game
terminates whatever strategy the player uses and however many heads grow back at each step. -/
theorem _root_.Frontier.Hydra_Kirby_Paris :
    ∀ f : ℕ → Hydra, ¬ ∀ n : ℕ, Move (f n) (f (n + 1)) := by
  intro f hf
  have key : ∀ h : Hydra, Acc (fun h' h => Move h h') h → ∀ n, f n ≠ h := by
    intro h hacc
    induction hacc with
    | intro x _ ih =>
      intro n hn
      exact ih (f (n + 1)) (by rw [← hn]; exact hf n) (n + 1) rfl
  exact key (f 0) (wellFounded_move.apply _) 0 rfl

/-- A hydra which is not dead admits a legal move: the game only gets stuck at `dead`. -/
theorem exists_move : ∀ {h : Hydra}, h ≠ dead → ∃ h', Move h h' := by
  intro h
  induction h using Hydra.rec (motive_2 := fun l => ∀ a ∈ l, a ≠ dead → ∃ a', Move a a') with
  | node l ih =>
    intro _
    match l with
    | [] => exact absurd rfl ‹Hydra.node [] ≠ dead›
    | c :: cs =>
      by_cases hc : c = dead
      · subst hc
        exact ⟨.node ([] ++ cs), by simpa using Move.chopHead [] cs⟩
      · obtain ⟨c', hc'⟩ := ih c (by simp) hc
        exact ⟨.node ([] ++ c' :: cs), by simpa using Move.deeper [] cs c c' hc'⟩
  | nil b hb _ => exact absurd hb (by simp)
  | cons a l iha ihl b hb hbd =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact iha hbd
    · exact ihl b hb hbd

/-- Iterating any legal strategy from any hydra reaches the dead hydra in finitely many
steps: the game terminates for every strategy. -/
theorem strategy_terminates (σ : Hydra → Hydra) (hσ : ∀ h, h ≠ dead → Move h (σ h))
    (h₀ : Hydra) : ∃ n : ℕ, σ^[n] h₀ = dead := by
  induction h₀ using WellFounded.induction wellFounded_move with
  | _ h ih =>
    by_cases hd : h = dead
    · exact ⟨0, by simpa using hd⟩
    · obtain ⟨n, hn⟩ := ih (σ h) (hσ h hd)
      exact ⟨n + 1, by rwa [Function.iterate_succ_apply]⟩

end Hydra

end Frontier

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

