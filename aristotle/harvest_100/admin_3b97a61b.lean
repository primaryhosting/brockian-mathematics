/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

We formalize the Kirby–Paris hydra game and prove that **every** play terminates,
no matter which head Hercules chops and no matter how many copies the hydra grows
at each stage (so, in particular, for every strategy).

A hydra is a finite rooted tree, encoded as `Hydra.node : List Hydra → Hydra`.
A *head* is a leaf.  In one move Hercules chops off a head; if the head has a
grandparent, the grandparent grows `n` extra copies of the subtree hanging at the
head's parent (with the head already removed).  The number `n` may be arbitrary
and may change from move to move.

The proof is the classical one: we attach to a hydra the ordinal
`o(node [h₁,…,h_k]) = ω ^ o(h₁) ♯ ⋯ ♯ ω ^ o(h_k) < ε₀`
(`♯` is the natural / Hessenberg sum) and check that every move strictly decreases
it; well-foundedness of the ordinals then finishes the argument.

The ordinal-arithmetic input that is not in Mathlib is that `ω ^ d` is closed under
natural sums; this is proved from scratch in the first section
(`Frontier.nadd_lt_opow_omega0`).

By the Kirby–Paris theorem this termination statement is not provable in Peano
arithmetic; the proof below is of course carried out in the ambient set theory of
Lean/Mathlib, where transfinite induction below ε₀ is available.
-/

open Ordinal NaturalOps

namespace Frontier

/-! ## Part 1: `ω ^ d` is closed under natural addition -/

/-- The key estimate: natural addition of two ordinals below `W * ω` is bounded by
the "Cantor-like" expression built from their quotients and remainders modulo `W`,
provided `W` itself is closed under natural addition. -/
theorem nadd_bound (W : Ordinal) (hW : W ≠ 0)
    (hCl : ∀ x y : Ordinal, x < W → y < W → x ♯ y < W) :
    ∀ a b : Ordinal, a < W * ω → b < W * ω →
      a ♯ b ≤ W * (a / W + b / W) + (a % W ♯ b % W) := by
  intro a
  induction a using Ordinal.induction with
  | h a IHa =>
  intro b
  induction b using Ordinal.induction with
  | h b IHb =>
  intro ha hb
  have hqa : a / W < ω := (Ordinal.div_lt hW).2 ha
  have hqb : b / W < ω := (Ordinal.div_lt hW).2 hb
  obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
  obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
  rw [Ordinal.nadd_le_iff]
  constructor
  · intro a' ha'
    have h1 := IHa a' ha' b (ha'.trans ha) hb
    have hq : a' / W ≤ a / W := Ordinal.div_le_left ha'.le _
    rcases lt_or_eq_of_le hq with hlt | heq
    · refine h1.trans_lt ?_
      have hr : a' % W ♯ b % W < W := hCl _ _ (Ordinal.mod_lt _ hW) (Ordinal.mod_lt _ hW)
      obtain ⟨na', hna'⟩ := Ordinal.lt_omega0.1 (hlt.trans hqa)
      have hlt' : na' < na := by rw [hna', hna] at hlt; exact_mod_cast hlt
      calc W * (a' / W + b / W) + (a' % W ♯ b % W)
          < W * (a' / W + b / W) + W := add_lt_add_right hr _
        _ = W * (a' / W + b / W + 1) := by rw [mul_add_one]
        _ ≤ W * (a / W + b / W) := by
            refine mul_le_mul_right ?_ W
            rw [hna, hnb, hna']
            have : (na' + nb + 1 : ℕ) ≤ na + nb := by omega
            exact_mod_cast this
        _ ≤ W * (a / W + b / W) + (a % W ♯ b % W) := le_self_add
    · refine h1.trans_lt ?_
      rw [heq]
      have hrlt : a' % W < a % W := by
        have e1 : W * (a / W) + a % W = a := Ordinal.div_add_mod a W
        have e2 : W * (a' / W) + a' % W = a' := Ordinal.div_add_mod a' W
        rw [heq] at e2
        have h3 : W * (a / W) + a' % W < W * (a / W) + a % W := by rw [e1, e2]; exact ha'
        exact lt_of_add_lt_add_left h3
      exact add_lt_add_right (Ordinal.nadd_lt_nadd_right hrlt _) _
  · intro b' hb'
    have h1 := IHb b' hb' ha (hb'.trans hb)
    have hq : b' / W ≤ b / W := Ordinal.div_le_left hb'.le _
    rcases lt_or_eq_of_le hq with hlt | heq
    · refine h1.trans_lt ?_
      have hr : a % W ♯ b' % W < W := hCl _ _ (Ordinal.mod_lt _ hW) (Ordinal.mod_lt _ hW)
      obtain ⟨nb', hnb'⟩ := Ordinal.lt_omega0.1 (hlt.trans hqb)
      have hlt' : nb' < nb := by rw [hnb', hnb] at hlt; exact_mod_cast hlt
      calc W * (a / W + b' / W) + (a % W ♯ b' % W)
          < W * (a / W + b' / W) + W := add_lt_add_right hr _
        _ = W * (a / W + b' / W + 1) := by rw [mul_add_one]
        _ ≤ W * (a / W + b / W) := by
            refine mul_le_mul_right ?_ W
            rw [hna, hnb, hnb']
            have : (na + nb' + 1 : ℕ) ≤ na + nb := by omega
            exact_mod_cast this
        _ ≤ W * (a / W + b / W) + (a % W ♯ b % W) := le_self_add
    · refine h1.trans_lt ?_
      rw [heq]
      have hrlt : b' % W < b % W := by
        have e1 : W * (b / W) + b % W = b := Ordinal.div_add_mod b W
        have e2 : W * (b' / W) + b' % W = b' := Ordinal.div_add_mod b' W
        rw [heq] at e2
        have h3 : W * (b / W) + b' % W < W * (b / W) + b % W := by rw [e1, e2]; exact hb'
        exact lt_of_add_lt_add_left h3
      exact add_lt_add_right (Ordinal.nadd_lt_nadd_left hrlt _) _

/-- If `W` is closed under natural addition, then so is `W * ω`. -/
theorem nadd_lt_mul_omega0 (W : Ordinal) (hW : W ≠ 0)
    (hCl : ∀ x y : Ordinal, x < W → y < W → x ♯ y < W) (a b : Ordinal)
    (ha : a < W * ω) (hb : b < W * ω) : a ♯ b < W * ω := by
  have h := nadd_bound W hW hCl a b ha hb
  have hqa : a / W < ω := (Ordinal.div_lt hW).2 ha
  have hqb : b / W < ω := (Ordinal.div_lt hW).2 hb
  obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
  obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
  have hr : a % W ♯ b % W < W := hCl _ _ (Ordinal.mod_lt _ hW) (Ordinal.mod_lt _ hW)
  refine h.trans_lt ?_
  calc W * (a / W + b / W) + (a % W ♯ b % W) < W * (a / W + b / W) + W :=
        add_lt_add_right hr _
    _ = W * (a / W + b / W + 1) := by rw [mul_add_one]
    _ < W * ω := by
        apply mul_lt_mul_of_pos_left _ (pos_iff_ne_zero.2 hW)
        rw [hna, hnb]
        have : ((na + nb + 1 : ℕ) : Ordinal) < ω := Ordinal.nat_lt_omega0 _
        simpa using this

/-- Every ordinal power `ω ^ d` is closed under natural (Hessenberg) addition. -/
theorem nadd_lt_opow_omega0 (d : Ordinal) :
    ∀ a b : Ordinal, a < ω ^ d → b < ω ^ d → a ♯ b < ω ^ d := by
  induction d using Ordinal.induction with
  | h d IH =>
  intro a b ha hb
  rcases Ordinal.zero_or_succ_or_isSuccLimit d with rfl | ⟨c, rfl⟩ | hlim
  · simp only [Ordinal.opow_zero, Ordinal.lt_one_iff_zero] at ha hb ⊢
    simp [ha, hb]
  · rw [Ordinal.opow_succ] at ha hb ⊢
    exact nadd_lt_mul_omega0 _ (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
      (IH c (Order.lt_succ c)) a b ha hb
  · rcases eq_zero_or_pos d with rfl | hd
    · simp only [Ordinal.opow_zero, Ordinal.lt_one_iff_zero] at ha hb ⊢
      simp [ha, hb]
    obtain ⟨e1, he1, ha1⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim).1 ha
    obtain ⟨e2, he2, hb1⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim).1 hb
    set e := max e1 e2 with he
    have hed : e < d := max_lt he1 he2
    have hae : a < ω ^ e * ω := by
      rw [← Ordinal.opow_succ]
      exact ha1.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos
        ((le_max_left e1 e2).trans (Order.le_succ e)))
    have hbe : b < ω ^ e * ω := by
      rw [← Ordinal.opow_succ]
      exact hb1.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos
        ((le_max_right e1 e2).trans (Order.le_succ e)))
    have hlt := nadd_lt_mul_omega0 (ω ^ e) (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
      (IH e hed) a b hae hbe
    rw [← Ordinal.opow_succ] at hlt
    exact hlt.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos (hlim.succ_lt hed).le)

/-! ## Part 2: hydras -/

/-- A hydra: a finite rooted tree, given by the list of the subtrees hanging at the root.
Heads are the leaves, i.e. the occurrences of `Hydra.node []`. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a single node with no heads left. -/
def dead : Hydra := .node []

mutual

/-- The ordinal `< ε₀` attached to a hydra:
`o (node [h₁,…,h_k]) = ω ^ o h₁ ♯ ⋯ ♯ ω ^ o h_k`. -/
noncomputable def ord : Hydra → Ordinal.{0}
  | .node l => ordList l

/-- The natural sum `ω ^ o h₁ ♯ ⋯ ♯ ω ^ o h_k` over a list of hydras. -/
noncomputable def ordList : List Hydra → Ordinal.{0}
  | [] => 0
  | h :: t => (ω ^ ord h) ♯ ordList t

end

@[simp] theorem ord_node (l : List Hydra) : ord (.node l) = ordList l := rfl

@[simp] theorem ordList_nil : ordList [] = 0 := rfl

@[simp] theorem ordList_cons (h : Hydra) (t : List Hydra) :
    ordList (h :: t) = (ω ^ ord h) ♯ ordList t := rfl

@[simp] theorem ord_dead : ord dead = 0 := rfl

theorem ordList_append (l₁ l₂ : List Hydra) :
    ordList (l₁ ++ l₂) = ordList l₁ ♯ ordList l₂ := by
  induction l₁ with
  | nil => simp
  | cons a t ih => simp [ih, Ordinal.nadd_assoc]

/-- A list of hydras all of whose entries have ordinal `< d` has natural sum `< ω ^ d`. -/
theorem ordList_lt_opow (d : Ordinal) (l : List Hydra) (hl : ∀ x ∈ l, ord x < d) :
    ordList l < ω ^ d := by
  induction l with
  | nil => simpa using Ordinal.opow_pos d Ordinal.omega0_pos
  | cons a t ih =>
      have ha : ω ^ ord a < ω ^ d :=
        (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (hl a (by simp))
      have ht : ordList t < ω ^ d := ih fun x hx => hl x (by simp [hx])
      simpa using nadd_lt_opow_omega0 d _ _ ha ht

/-! ### The moves of the game -/

/-- `ChopHead h h'`: `h'` is obtained from `h` by chopping off a head (a leaf)
which is a child of the root of `h`. -/
inductive ChopHead : Hydra → Hydra → Prop
  | mk (pre post : List Hydra) :
      ChopHead (.node (pre ++ .node [] :: post)) (.node (pre ++ post))

/-- `DeepStep n h h'`: `h'` results from `h` by chopping a head at depth `≥ 2`,
the grandparent of the chopped head growing `n` extra copies of the head's parent.

* `copy`: the chopped head lies at depth `2`, i.e. its parent `c` is a child of the
  root; the root, being the grandparent, then carries `n + 1` copies of `c` with that
  head removed (the original one, and `n` new ones).
* `deep`: the chopped head lies at depth `≥ 3`, so the whole move, copies included,
  happens inside a single child of the root. -/
inductive DeepStep (n : ℕ) : Hydra → Hydra → Prop
  | copy (pre post : List Hydra) {c c' : Hydra} : ChopHead c c' →
      DeepStep n (.node (pre ++ c :: post)) (.node (pre ++ List.replicate (n + 1) c' ++ post))
  | deep (pre post : List Hydra) {c c' : Hydra} : DeepStep n c c' →
      DeepStep n (.node (pre ++ c :: post)) (.node (pre ++ c' :: post))

/-- `Step n h h'`: `h'` results from `h` by one legal move of the hydra game in which
the hydra grows `n` extra copies.  Either Hercules chops a head attached directly to
the root (such a head has no grandparent, so nothing grows back), or he chops a head
at depth `≥ 2`, whose grandparent then grows `n` copies of the head's parent. -/
def Step (n : ℕ) (h h' : Hydra) : Prop := ChopHead h h' ∨ DeepStep n h h'

/-- Chopping a head strictly decreases the ordinal of a hydra. -/
theorem ord_lt_of_chopHead {h h' : Hydra} (hc : ChopHead h h') : ord h' < ord h := by
  cases hc with
  | mk pre post =>
      simp only [ord_node, ordList_append, ordList_cons, ord_node, ordList_nil,
        Ordinal.opow_zero]
      refine Ordinal.nadd_lt_nadd_left ?_ _
      rw [Ordinal.one_nadd]
      exact Order.lt_succ _

/-- A chop at depth `≥ 2`, copies included, strictly decreases the ordinal of a hydra. -/
theorem ord_lt_of_deepStep {n : ℕ} {h h' : Hydra} (hs : DeepStep n h h') : ord h' < ord h := by
  induction hs with
  | copy pre post hc =>
      rename_i c c'
      have hcc : ord c' < ord c := ord_lt_of_chopHead hc
      have hrep : ordList (List.replicate (n + 1) c') < ω ^ ord c := by
        refine ordList_lt_opow _ _ ?_
        intro x hx
        rw [List.eq_of_mem_replicate hx]
        exact hcc
      simp only [ord_node, ordList_append, ordList_cons, Ordinal.nadd_assoc]
      exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right hrep _) _
  | deep pre post _ ih =>
      simp only [ord_node, ordList_append, ordList_cons]
      refine Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right ?_ _) _
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 ih

/-- Every move of the hydra game strictly decreases the ordinal of the hydra. -/
theorem ord_lt_of_step {n : ℕ} {h h' : Hydra} (hs : Step n h h') : ord h' < ord h := by
  rcases hs with hc | hd
  · exact ord_lt_of_chopHead hc
  · exact ord_lt_of_deepStep hd

/-- Induction principle for hydras: to prove a statement for every hydra it suffices
to prove it for `node l` assuming it for all members of `l`. -/
theorem induction_on {P : Hydra → Prop} (H : ∀ l : List Hydra, (∀ x ∈ l, P x) → P (.node l)) :
    ∀ t : Hydra, P t := by
  intro t
  induction t using Hydra.rec (motive_2 := fun l => ∀ x ∈ l, P x) with
  | node l ih => exact H l ih
  | nil => rename_i x hx; cases hx
  | cons a t iha iht =>
      rename_i x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact iha
      · exact iht x hx'

/-- As long as the hydra is not dead, Hercules has a move available.  Together with
`Frontier.Hydra_Kirby_Paris` this says that the game really is a terminating game:
plays can always be continued until, after finitely many moves, the hydra is dead. -/
theorem exists_step_of_ne_dead (n : ℕ) :
    ∀ h : Hydra, h ≠ dead → ∃ h', Step n h h' := by
  refine induction_on ?_
  intro l IH hne
  match l with
  | [] => exact absurd rfl hne
  | (.node []) :: t =>
      exact ⟨.node t, Or.inl (ChopHead.mk [] t)⟩
  | (.node (d :: u)) :: t =>
      obtain ⟨c', hc'⟩ := IH (.node (d :: u)) (by simp) (by simp [dead])
      rcases hc' with hchop | hdeep
      · exact ⟨.node (List.replicate (n + 1) c' ++ t),
          Or.inr (DeepStep.copy [] t hchop)⟩
      · exact ⟨.node (c' :: t), Or.inr (DeepStep.deep [] t hdeep)⟩

end Hydra

/-- **The hydra game is well-founded**: the relation "`h'` is obtainable from `h`
by one move" (with an arbitrary number of grown copies) admits no infinite descent. -/
theorem hydra_step_wf : WellFounded (fun h' h : Hydra => ∃ n, Hydra.Step n h h') := by
  have hwf : WellFounded (InvImage ((· < ·) : Ordinal → Ordinal → Prop) Hydra.ord) :=
    InvImage.wf _ (Ordinal.lt_wf)
  refine Subrelation.wf ?_ hwf
  rintro h' h ⟨n, hs⟩
  exact Hydra.ord_lt_of_step hs

/-- **Kirby–Paris hydra theorem.**  Every play of the hydra game terminates:
if `h 0, h 1, h 2, …` is any play — at each stage Hercules chops off an arbitrary
head of the current hydra, which then grows an arbitrary number `n i` of copies,
as long as the hydra is not yet dead — then the hydra is dead at some stage `N`.

Since the choice of head and the number of copies are arbitrary at every stage,
this covers every strategy for Hercules and every growth schedule for the hydra.
(By the Kirby–Paris theorem this statement is not provable in Peano arithmetic.) -/
theorem Hydra_Kirby_Paris (h : ℕ → Hydra) (n : ℕ → ℕ)
    (hplay : ∀ i, h i ≠ Hydra.dead → Hydra.Step (n i) (h i) (h (i + 1))) :
    ∃ N, h N = Hydra.dead := by
  by_contra hcon
  push_neg at hcon
  have hdec : ∀ i, Hydra.ord (h (i + 1)) < Hydra.ord (h i) := fun i =>
    Hydra.ord_lt_of_step (hplay i (hcon i))
  have key : ∀ x : Ordinal, ∀ i, Hydra.ord (h i) ≠ x := by
    intro x
    induction x using Ordinal.induction with
    | h j IH => intro i hij; exact IH (Hydra.ord (h (i + 1))) (hij ▸ hdec i) (i + 1) rfl
  exact key (Hydra.ord (h 0)) 0 rfl

/-! ### Sanity checks: the moves are the intended ones -/

/-- Chopping one of the two heads attached to the root: no copies are grown. -/
example : Hydra.Step 5 (.node [.node [], .node []]) (.node [.node []]) :=
  Or.inl (Hydra.ChopHead.mk [] [.node []])

/-- Chopping the head of the path of length two, with `n = 2`: the root, being the
grandparent of the chopped head, ends up carrying `3 = 2 + 1` copies of the (now
headless) parent, i.e. three heads. -/
example : Hydra.Step 2 (.node [.node [.node []]]) (.node [.node [], .node [], .node []]) := by
  have h : Hydra.DeepStep 2 (.node ([] ++ (.node [.node []]) :: []))
      (.node ([] ++ List.replicate 3 (.node []) ++ [])) :=
    Hydra.DeepStep.copy [] [] (Hydra.ChopHead.mk [] [])
  simpa [List.replicate] using Or.inr h

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

