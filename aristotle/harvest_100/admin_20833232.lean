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
namespace KirbyParis

/-!
## Hydras

A *hydra* is a finite rooted tree.  We encode it as an inductive type whose only
constructor takes the (ordered) list of subtrees hanging off the root; the order of the
list carries no meaning, and all statements below are invariant under permuting it.
-/

/-- A hydra: a finite rooted tree, given by the list of subtrees attached to its root. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a bare root with no heads. -/
def dead : Hydra := .node []

end Hydra

/-- Structural induction for `Hydra`: to prove a property of every hydra it suffices to
prove it for `node ts` assuming it for every subtree in `ts`. -/
@[elab_as_elim]
theorem Hydra.strong_induction {P : Hydra → Prop}
    (h : ∀ ts : List Hydra, (∀ t ∈ ts, P t) → P (Hydra.node ts)) : ∀ x, P x :=
  Hydra.rec (motive_1 := P) (motive_2 := fun ts => ∀ t ∈ ts, P t)
    (fun ts ih => h ts ih)
    (fun t ht => absurd ht List.not_mem_nil)
    (fun a l ha hl t ht => by
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ha
      · exact hl t ht)

/-!
## The moves of the Kirby–Paris hydra game

Hercules chops off a *head*, i.e. a leaf of the tree.

* If the head grows directly out of the root, it is simply removed (`Chop`).
* Otherwise the head has a parent `t` and a grandparent.  The head is removed from `t`,
  producing `t'`, and then the grandparent grows some number `k` of copies of `t'` in place
  of `t`.  (The classical rule takes `k = n + 1` at stage `n`; we allow an *arbitrary*
  `k : ℕ`, which makes the termination theorem below strictly stronger.)

`Deep` describes the second kind of move, by recursion on the distance from the root.
-/

/-- `Chop h h'` : `h'` is obtained from `h` by cutting off a head that grows directly out of
the root of `h`. -/
inductive Chop : Hydra → Hydra → Prop
  | mk (l₁ l₂ : List Hydra) :
      Chop (.node (l₁ ++ .node [] :: l₂)) (.node (l₁ ++ l₂))

/-- `Deep h h'` : `h'` is obtained from `h` by cutting off a head at distance at least `2`
from the root, together with the Kirby–Paris duplication at the grandparent of that head. -/
inductive Deep : Hydra → Hydra → Prop
  /-- The cut head is at distance exactly `2`: it is chopped off the child `t`, turning `t`
  into `t'`, and the root (the grandparent) then carries `k` copies of `t'` instead of `t`. -/
  | dup (l₁ l₂ : List Hydra) (t t' : Hydra) (k : ℕ) (h : Chop t t') :
      Deep (.node (l₁ ++ t :: l₂)) (.node (l₁ ++ List.replicate k t' ++ l₂))
  /-- The cut head is at distance at least `3`: the whole move takes place inside a single
  child `t` of the root. -/
  | nest (l₁ l₂ : List Hydra) (t t' : Hydra) (h : Deep t t') :
      Deep (.node (l₁ ++ t :: l₂)) (.node (l₁ ++ t' :: l₂))

/-- `Move h h'` : `h'` results from `h` by one legal move of the Kirby–Paris hydra game. -/
def Move (h h' : Hydra) : Prop := Chop h h' ∨ Deep h h'

/-!
## A well-founded relation on hydras

We compare hydras by the relation `HR`, a "one-step" version of the Cantor-normal-form
order: `HR h' h` holds when the multiset of subtrees of `h'` is obtained from that of `h`
by deleting one subtree `a` and inserting finitely many subtrees, each `HR`-smaller than
`a`.  This is exactly `Relation.CutExpand HR` applied to the multisets of children, so
Mathlib's `Acc.cutExpand` / `Relation.acc_of_singleton` (from `Mathlib/Logic/Hydra.lean`,
the *simple* hydra game) can be used to run the induction.
-/

/-- The one-step Cantor-normal-form ordering on hydras. -/
inductive HR : Hydra → Hydra → Prop
  | mk {ts' ts : List Hydra} (u : Multiset Hydra) (a : Hydra) :
      (∀ a' ∈ u, HR a' a) →
      ((ts' : Multiset Hydra) + {a} = (ts : Multiset Hydra) + u) →
      HR (.node ts') (.node ts)

theorem HR_irrefl : ∀ x y : Hydra, HR x y → x ≠ y := by
  intro x y h
  induction h with
  | @mk ts' ts u a hu he ih =>
    intro hxy
    have hts : ts' = ts := by injection hxy
    subst hts
    have hu' : ({a} : Multiset Hydra) = u := add_left_cancel he
    exact ih a (hu' ▸ Multiset.mem_singleton_self a) rfl

instance : Std.Irrefl HR := ⟨fun a h => HR_irrefl a a h rfl⟩

private theorem acc_node_of_acc_cutExpand {s : Multiset Hydra}
    (hs : Acc (Relation.CutExpand HR) s) :
    ∀ ts : List Hydra, (ts : Multiset Hydra) = s → Acc HR (.node ts) := by
  induction hs with
  | intro s _ ih =>
    intro ts hts
    refine Acc.intro _ ?_
    rintro y hy
    cases hy with
    | @mk ts' _ u a hu he =>
      exact ih _ (hts ▸ (⟨u, a, hu, he⟩ : Relation.CutExpand HR _ _)) ts' rfl

/-- The ordering `HR` on hydras is well-founded.  This is the combinatorial heart of the
Kirby–Paris theorem; it is deduced from Mathlib's `Relation.acc_of_singleton` and
`Acc.cutExpand`. -/
theorem HR_wf : WellFounded HR := by
  refine ⟨?_⟩
  intro x
  induction x using Hydra.strong_induction with
  | _ ts ih =>
    refine acc_node_of_acc_cutExpand ?_ ts rfl
    exact Relation.acc_of_singleton (fun a ha => (ih a (by simpa using ha)).cutExpand)

/-! ### Multiset bookkeeping -/

private theorem coe_append_cons (l₁ l₂ : List Hydra) (x : Hydra) :
    ((l₁ ++ x :: l₂ : List Hydra) : Multiset Hydra) = (l₁ : Multiset Hydra) + {x} + l₂ :=
  (add_assoc (l₁ : Multiset Hydra) {x} (l₂ : Multiset Hydra)).symm

private theorem coe_append_append (l₁ m l₂ : List Hydra) :
    ((l₁ ++ m ++ l₂ : List Hydra) : Multiset Hydra)
      = (l₁ : Multiset Hydra) + (m : Multiset Hydra) + l₂ := rfl

private theorem coe_replicate (k : ℕ) (x : Hydra) :
    ((List.replicate k x : List Hydra) : Multiset Hydra) = Multiset.replicate k x := rfl

/-! ### Every move strictly decreases a hydra -/

/-- Chopping a head off the root strictly decreases the hydra. -/
theorem HR_of_chop {t t' : Hydra} (h : Chop t t') : HR t' t := by
  cases h with
  | mk l₁ l₂ =>
    refine HR.mk 0 (.node []) (by simp) ?_
    rw [coe_append_cons]
    show ((l₁ : Multiset Hydra) + l₂) + {Hydra.node []}
      = ((l₁ : Multiset Hydra) + {Hydra.node []} + l₂) + 0
    abel

/-- `HR` is compatible with replacing one child of the root. -/
theorem HR_child {s s' : Hydra} (h : HR s' s) (l₁ l₂ : List Hydra) :
    HR (.node (l₁ ++ s' :: l₂)) (.node (l₁ ++ s :: l₂)) := by
  refine HR.mk {s'} s ?_ ?_
  · intro a' ha'
    rw [Multiset.mem_singleton] at ha'
    exact ha' ▸ h
  · rw [coe_append_cons, coe_append_cons]
    abel

/-- Replacing one child `t` of the root by any number of copies of a strictly smaller
hydra `t'` strictly decreases the hydra. -/
theorem HR_dup {t t' : Hydra} (h : HR t' t) (l₁ l₂ : List Hydra) (k : ℕ) :
    HR (.node (l₁ ++ List.replicate k t' ++ l₂)) (.node (l₁ ++ t :: l₂)) := by
  refine HR.mk (Multiset.replicate k t') t ?_ ?_
  · intro a' ha'
    exact (Multiset.eq_of_mem_replicate ha') ▸ h
  · rw [coe_append_append, coe_append_cons, coe_replicate]
    abel

/-- Every deep move (cut at distance ≥ 2, with duplication) strictly decreases the hydra,
in the transitive closure of `HR`. -/
theorem transGen_HR_of_deep {t t' : Hydra} (h : Deep t t') :
    Relation.TransGen HR t' t := by
  induction h with
  | dup l₁ l₂ t t' k hc =>
    exact Relation.TransGen.single (HR_dup (HR_of_chop hc) l₁ l₂ k)
  | nest l₁ l₂ t t' _ ih =>
    exact Relation.TransGen.lift (fun s => Hydra.node (l₁ ++ s :: l₂))
      (fun _ _ hab => HR_child hab l₁ l₂) ih

/-- Every legal move of the Kirby–Paris hydra game strictly decreases the hydra with
respect to the well-founded relation `HR`. -/
theorem transGen_HR_of_move {h h' : Hydra} (hm : Move h h') :
    Relation.TransGen HR h' h := by
  rcases hm with hc | hd
  · exact Relation.TransGen.single (HR_of_chop hc)
  · exact transGen_HR_of_deep hd

/-! ### Legal moves exist as long as the hydra is alive -/

/-- A hydra which is not yet dead admits a legal move. -/
theorem exists_move : ∀ h : Hydra, h ≠ Hydra.dead → ∃ h', Move h h' := by
  intro h
  induction h using Hydra.strong_induction with
  | _ ts ih =>
    intro hne
    match ts, ih with
    | [], _ => exact absurd rfl hne
    | (t :: rest), ih =>
      by_cases ht : t = Hydra.dead
      · subst ht
        exact ⟨.node ([] ++ rest), Or.inl (Chop.mk [] rest)⟩
      · obtain ⟨t', ht'⟩ := ih t List.mem_cons_self ht
        rcases ht' with hc | hd
        · exact ⟨.node ([] ++ List.replicate 1 t' ++ rest),
            Or.inr (Deep.dup [] rest t t' 1 hc)⟩
        · exact ⟨.node ([] ++ t' :: rest), Or.inr (Deep.nest [] rest t t' hd)⟩

/-! ### Sanity checks: the rules really are the Kirby–Paris rules -/

/-- Cutting the single head of the one-headed hydra kills it. -/
example : Move (.node [Hydra.dead]) Hydra.dead := Or.inl (Chop.mk [] [])

/-- The hydra `root — v — head` of height two: cutting its unique head makes the root grow
`k` bare heads, for an arbitrary `k`.  This is the duplication rule. -/
example (k : ℕ) :
    Move (.node [.node [Hydra.dead]]) (.node (List.replicate k Hydra.dead)) := by
  refine Or.inr ?_
  have := Deep.dup [] [] (.node [Hydra.dead]) Hydra.dead k (Chop.mk [] [])
  simpa using this

/-! ### Termination -/

/-- The "hydra shrinks" relation is well-founded. -/
theorem move_wf : WellFounded (fun h' h : Hydra => Move h h') :=
  Subrelation.wf transGen_HR_of_move HR_wf.transGen

end KirbyParis

open KirbyParis in
/-- **Kirby–Paris hydra theorem.**  Every play of the Kirby–Paris hydra game terminates,
no matter which head Hercules cuts and no matter how many copies the hydra grows.

The statement is packaged as three equivalent faces of termination:

1. the relation "`h'` is reachable from `h` by one legal move" is well-founded;
2. there is no infinite play, i.e. no infinite sequence of legal moves;
3. for *every* strategy `s` (a function choosing a legal move at each living hydra) and
   every starting hydra `h`, iterating `s` reaches the dead hydra after finitely many
   steps.

Together with `Frontier.KirbyParis.exists_move` (a living hydra always admits a legal
move) this says that Hercules always wins.

This is the Kirby–Paris theorem, which is true but unprovable in Peano arithmetic; the
proof below is of course carried out in ZFC, where the required transfinite induction is
available. -/
theorem Hydra_Kirby_Paris :
    WellFounded (fun h' h : Hydra => Move h h') ∧
    (∀ p : ℕ → Hydra, ¬ ∀ i : ℕ, Move (p i) (p (i + 1))) ∧
    (∀ s : Hydra → Hydra, (∀ g : Hydra, g ≠ Hydra.dead → Move g (s g)) →
      ∀ h : Hydra, ∃ N : ℕ, s^[N] h = Hydra.dead) := by
  refine ⟨move_wf, ?_, ?_⟩
  · intro p hp
    have key : ∀ x : Hydra, Acc (fun h' h : Hydra => Move h h') x → ∀ i : ℕ, p i ≠ x := by
      intro x hx
      induction hx with
      | intro y _ ih =>
        rintro i rfl
        exact ih (p (i + 1)) (hp i) (i + 1) rfl
    exact key (p 0) (move_wf.apply _) 0 rfl
  · intro s hs h
    induction h using move_wf.induction with
    | _ h ih =>
      by_cases hd : h = Hydra.dead
      · exact ⟨0, by simpa using hd⟩
      · obtain ⟨N, hN⟩ := ih (s h) (hs h hd)
        exact ⟨N + 1, by rwa [Function.iterate_succ_apply]⟩

end Frontier

