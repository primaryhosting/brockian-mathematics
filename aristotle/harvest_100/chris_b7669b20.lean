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

/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated as a module docstring after the imports; Lean does not
-- allow a `/-!` doc comment to precede the `import` commands.)

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Kirby–Paris hydra theorem

A *hydra* is a finite rooted tree, modelled here by the nested inductive type `Hydra`
(a node carries the list of its children; the intended semantics is that the order of the
children is irrelevant, so all statements below are phrased in terms of the *multiset* of
children).

Hercules fights the hydra by chopping off a *head*, i.e. a leaf of the tree at distance at
least one from the root.

* If the head is a child of the root it is simply removed (`Hydra.Chop`).
* Otherwise, let `c` be the parent of the head, and let `c'` be `c` with the head removed.
  The hydra grows back: `c` is replaced, among the children of its own parent (the
  grandparent of the head), by `n + 1` copies of `c'`, where `n` is arbitrary and may depend
  on the stage of the game (`Hydra.Deep.grand`, propagated upwards by `Hydra.Deep.inner`).

`Hydra.Move n` is the union of these two kinds of moves.  The theorem of Kirby and Paris
states that Hercules always wins, no matter which heads he chops and no matter how fast the
hydra grows.  This is `Frontier.Hydra_Kirby_Paris` below: for every sequence of hydras in
which each hydra is obtained from the previous one by a legal move as long as the hydra is
still alive, the dead hydra `Hydra.dead` (a single root with no children) is reached after
finitely many steps.

(The Kirby–Paris theorem is famously *not* provable in Peano arithmetic; that
independence result is a statement about PA and is not formalized here.  The proof given
below is the usual one, carried out in the ambient set theory of Lean/Mathlib: hydras are
ordered by the "nested multiset" ordering `Hydra.HLT`, whose well-foundedness is obtained
from the well-foundedness of `Relation.CutExpand` — the multiset hydra game of
`Mathlib/Logic/Hydra.lean` — by induction on the tree, and every legal move strictly
decreases a hydra in this ordering.)
-/

namespace Frontier

/-- A hydra: a finite rooted tree, given by the list of the subtrees hanging at the root.
The order of the children is irrelevant, and all notions below only depend on the
*multiset* of children. -/
inductive Hydra where
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a root with no children. -/
def dead : Hydra := node []

/-- `Chop h h'` means that `h'` is obtained from `h` by cutting off a head which is a child
of the root of `h`, i.e. by deleting one childless child of the root. -/
inductive Chop : Hydra → Hydra → Prop
  | mk {l l' : List Hydra} (he : (l : Multiset Hydra) = dead ::ₘ (l' : Multiset Hydra)) :
      Chop (node l) (node l')

/-- `Deep n h h'` means that `h'` is obtained from `h` by cutting off a head at distance at
least `2` from the root, the hydra growing back `n` extra copies of the (modified) parent of
the head at the grandparent of the head. -/
inductive Deep (n : ℕ) : Hydra → Hydra → Prop
  /-- The head is a grandchild of the root: its parent `c` becomes `c'`, and `n + 1` copies
  of `c'` are attached to the root in place of `c`. -/
  | grand {l l' : List Hydra} {m : Multiset Hydra} {c c' : Hydra}
      (h1 : (l : Multiset Hydra) = c ::ₘ m) (hc : Chop c c')
      (h2 : (l' : Multiset Hydra) = Multiset.replicate (n + 1) c' + m) : Deep n (node l) (node l')
  /-- The head is deeper: the move takes place inside a single child `c` of the root. -/
  | inner {l l' : List Hydra} {m : Multiset Hydra} {c c' : Hydra}
      (h1 : (l : Multiset Hydra) = c ::ₘ m) (hd : Deep n c c')
      (h2 : (l' : Multiset Hydra) = c' ::ₘ m) : Deep n (node l) (node l')

/-- A legal move of the hydra game, where the hydra grows back `n` extra copies. -/
def Move (n : ℕ) (h h' : Hydra) : Prop := Chop h h' ∨ Deep n h h'

/-!
### The nested multiset ordering on hydras
-/

/-- The nested multiset ordering: `HLT h' h` if the multiset of children of `h'` is obtained
from the multiset of children of `h` by removing one child `a` and adding back finitely many
hydras, each `HLT`-smaller than `a`.  (This is `Relation.CutExpand HLT` on the children, see
`Hydra.HLT_iff_cutExpand`.) -/
inductive HLT : Hydra → Hydra → Prop
  | intro {l m : List Hydra} {t : Multiset Hydra} {a : Hydra}
      (ht : ∀ a' ∈ t, HLT a' a)
      (he : (l : Multiset Hydra) + {a} = (m : Multiset Hydra) + t) :
      HLT (node l) (node m)

theorem HLT_iff_cutExpand {l m : List Hydra} :
    HLT (node l) (node m) ↔
      Relation.CutExpand HLT (l : Multiset Hydra) (m : Multiset Hydra) := by
  constructor
  · rintro ⟨ht, he⟩
    exact ⟨_, _, ht, he⟩
  · rintro ⟨t, a, ht, he⟩
    exact HLT.intro ht he

theorem HLT.ne : ∀ {x y : Hydra}, HLT x y → x ≠ y := by
  intro x y h
  induction h with
  | @intro l m t a ht he ih =>
    intro hxy
    have hlm : l = m := by injection hxy
    subst hlm
    have hta : ({a} : Multiset Hydra) = t := add_left_cancel he
    exact ih a (by rw [← hta]; simp) rfl

instance : Std.Irrefl HLT := ⟨fun _ h => h.ne rfl⟩

/-- If the multiset of children of a hydra is accessible for the multiset hydra game
`Relation.CutExpand HLT`, then the hydra itself is accessible for `HLT`. -/
theorem acc_node_of_acc_children {s : Multiset Hydra} (hs : Acc (Relation.CutExpand HLT) s) :
    ∀ l : List Hydra, (l : Multiset Hydra) = s → Acc HLT (node l) := by
  induction hs with
  | intro s _ ih =>
    intro l hl
    refine Acc.intro _ ?_
    rintro y hy
    cases hy with
    | @intro l₀ _m t a ht he =>
      exact ih (l₀ : Multiset Hydra) ⟨t, a, ht, by rw [he, hl]⟩ l₀ rfl

/-- Every hydra is accessible for the nested multiset ordering. -/
theorem HLT_acc (h : Hydra) : Acc HLT h :=
  Hydra.rec (motive_1 := fun h => Acc HLT h) (motive_2 := fun l => ∀ x ∈ l, Acc HLT x)
    (fun l ih => acc_node_of_acc_children
      (Relation.acc_of_singleton (fun a ha => Acc.cutExpand (ih a (by simpa using ha)))) l rfl)
    (fun x hx => absurd hx (List.not_mem_nil))
    (fun _ _ ihh iht x hx => by
      rcases List.mem_cons.1 hx with rfl | h
      · exact ihh
      · exact iht x h)
    h

/-- The nested multiset ordering on hydras is well-founded. -/
theorem HLT_wf : WellFounded HLT := ⟨HLT_acc⟩

/-!
### Every legal move decreases the hydra
-/

theorem HLT_of_chop {h h' : Hydra} (hc : Chop h h') : HLT h' h := by
  cases hc with
  | @mk l l' he =>
    refine HLT.intro (t := 0) (a := dead) (by simp) ?_
    rw [he]
    simp [← Multiset.singleton_add]
    abel

theorem HLT_of_deep {n : ℕ} {h h' : Hydra} (hd : Deep n h h') : HLT h' h := by
  induction hd with
  | @grand l l' m c c' h1 hc h2 =>
    refine HLT.intro (t := Multiset.replicate (n + 1) c') (a := c) ?_ ?_
    · intro a' ha'
      rw [Multiset.eq_of_mem_replicate ha']
      exact HLT_of_chop hc
    · rw [h1, h2, ← Multiset.singleton_add]
      abel
  | @inner l l' m c c' h1 _ h2 ih =>
    refine HLT.intro (t := {c'}) (a := c) ?_ ?_
    · intro a' ha'
      rw [Multiset.mem_singleton.1 ha']
      exact ih
    · rw [h1, h2, ← Multiset.singleton_add, ← Multiset.singleton_add]
      abel

/-- Every legal move strictly decreases the hydra in the nested multiset ordering. -/
theorem HLT_of_move {n : ℕ} {h h' : Hydra} (hm : Move n h h') : HLT h' h :=
  hm.elim HLT_of_chop HLT_of_deep

/-- The hydra game is well-founded: the relation "`h'` can be obtained from `h` by one legal
move" has no infinite descending chains. -/
theorem move_wf : WellFounded (fun h' h => ∃ n, Move n h h') :=
  Subrelation.wf (fun ⟨_, hm⟩ => HLT_of_move hm) HLT_wf

/-!
### There is always a legal move as long as the hydra is alive
-/

theorem exists_deep_of_mem {n : ℕ} :
    ∀ (c : Hydra), c ≠ dead → ∀ (l : List Hydra), c ∈ l → ∃ h', Deep n (node l) h' := by
  refine Hydra.rec (motive_1 := fun c => c ≠ dead → ∀ l : List Hydra, c ∈ l →
      ∃ h', Deep n (node l) h')
    (motive_2 := fun k => ∀ d ∈ k, d ≠ dead → ∀ l : List Hydra, d ∈ l →
      ∃ h', Deep n (node l) h')
    ?_ ?_ ?_
  · rintro (_ | ⟨d, k⟩) ih hne l hl
    · exact absurd rfl hne
    · obtain ⟨s, t, rfl⟩ := List.append_of_mem hl
      have hcoe : ((s ++ node (d :: k) :: t : List Hydra) : Multiset Hydra)
          = node (d :: k) ::ₘ ((s ++ t : List Hydra) : Multiset Hydra) := by
        rw [Multiset.cons_coe]
        exact Multiset.coe_eq_coe.2 List.perm_middle
      by_cases hd : d = dead
      · subst hd
        refine ⟨node (List.replicate (n + 1) (node k) ++ (s ++ t)), ?_⟩
        refine Deep.grand (c := node (dead :: k)) (c' := node k) hcoe (Chop.mk (by simp)) ?_
        rw [← Multiset.coe_add, Multiset.coe_replicate]
      · obtain ⟨c', hc'⟩ := ih d List.mem_cons_self hd (d :: k) List.mem_cons_self
        exact ⟨node (c' :: (s ++ t)), Deep.inner hcoe hc' (by simp)⟩
  · exact fun d hd => absurd hd (List.not_mem_nil)
  · intro hd tl ihh iht d hmem
    rcases List.mem_cons.1 hmem with rfl | h
    · exact ihh
    · exact iht d h

/-- As long as the hydra is not dead, Hercules can chop off a head. -/
theorem exists_move {n : ℕ} {h : Hydra} (hh : h ≠ dead) : ∃ h', Move n h h' := by
  obtain ⟨l⟩ := h
  match l with
  | [] => exact absurd rfl hh
  | c :: k =>
    by_cases hc : c = dead
    · subst hc
      exact ⟨node k, Or.inl (Chop.mk (by simp))⟩
    · obtain ⟨h', hh'⟩ := exists_deep_of_mem (n := n) c hc (c :: k) List.mem_cons_self
      exact ⟨h', Or.inr hh'⟩

/-- A sanity check: chopping the unique head of the hydra with one child carrying one leaf,
with regrowth parameter `n = 2`, produces the hydra whose root has three leaves. -/
example : Move 2 (node [node [dead]]) (node [dead, dead, dead]) :=
  Or.inr (Deep.grand (c := node [dead]) (c' := dead) (m := 0) (by simp)
    (Chop.mk (l' := []) (by simp [dead])) (by rw [add_zero]; rfl))

end Hydra

/-- A well-founded relation admits no infinite descending sequence. -/
theorem no_descending_seq {α : Type*} {r : α → α → Prop} (hwf : WellFounded r) (f : ℕ → α)
    (hf : ∀ k, r (f (k + 1)) (f k)) : False := by
  have key : ∀ x : α, Acc r x → ∀ g : ℕ → α, (∀ k, r (g (k + 1)) (g k)) → g 0 ≠ x := by
    intro x hx
    induction hx with
    | intro y _ ih =>
      intro g hg hgy
      exact ih (g 1) (by rw [← hgy]; exact hg 0) (fun k => g (k + 1)) (fun k => hg (k + 1)) rfl
  exact key (f 0) (hwf.apply _) f hf rfl

/-- **The Kirby–Paris hydra theorem**: every hydra game terminates, for any strategy.

If `f : ℕ → Hydra` is a play of the hydra game, i.e. `f (k + 1)` is obtained from `f k` by a
legal move (with an arbitrary number `n k` of regrown copies) whenever `f k` is still alive,
then the hydra is dead after finitely many steps.  No assumption whatsoever is made on how
the heads are chosen (the strategy) or on how fast the hydra grows.

(The Kirby–Paris independence of this statement from Peano arithmetic is not formalized.) -/
theorem Hydra_Kirby_Paris (n : ℕ → ℕ) (f : ℕ → Hydra)
    (hf : ∀ k, f k ≠ Hydra.dead → Hydra.Move (n k) (f k) (f (k + 1))) :
    ∃ N, f N = Hydra.dead := by
  by_contra hcon
  push_neg at hcon
  exact no_descending_seq Hydra.HLT_wf f fun k => Hydra.HLT_of_move (hf k (hcon k))

end Frontier

