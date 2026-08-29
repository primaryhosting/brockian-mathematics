/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command of a file, so the header above is a plain
-- block comment rather than a `/-!` module docstring; its text is otherwise verbatim.)

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

We formalise Kirby–Paris hydras and the statement that *every* hydra game terminates, no matter
which head Hercules chops and no matter how fast the hydra grows new heads.

* A hydra is a finite rooted tree, `Hydra.node : List Hydra → Hydra` (the list of subtrees is
  considered up to permutation; all our relations are closed under permutations of children).
* `Hydra.Move n a b` says that `b` is obtained from `a` by one move of the game: Hercules chops
  off a head (a leaf) of `a`, and if the chopped leaf had a grandparent, `n` extra copies of the
  (already modified) parent subtree are grown at that grandparent.
* The main theorem `Frontier.Hydra_Kirby_Paris` states that there is no infinite play (for any
  choice of moves and any growth rates `k i`), and consequently that every strategy kills the
  hydra in finitely many steps.

The proof assigns to each hydra its ordinal `Hydra.ord < ε₀`, in Cantor normal form built with
the *natural* (Hessenberg) sum `♯`, and shows that every move strictly decreases this ordinal.
The key ordinal-arithmetic ingredient, proved here from scratch, is that `ω ^ b` is closed under
natural addition (`KirbyParis.nadd_lt_opow`).
-/

open Ordinal
open scoped NaturalOps

namespace KirbyParis

/-! ### Powers of `ω` are closed under natural addition -/

/-- Bookkeeping step used in `KirbyParis.key`. -/
theorem bound_lt (c : Ordinal)
    (hIH : ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c → x ♯ y < ω ^ c)
    (p' p q : ℕ) (x' x y u : Ordinal) (hx' : x' < ω ^ c) (hy : y < ω ^ c)
    (hu : u ≤ ω ^ c * (p' + q : ℕ) + (x' ♯ y))
    (h : p' < p ∨ (p' = p ∧ x' < x)) :
    u < ω ^ c * (p + q : ℕ) + (x ♯ y) := by
  rcases h with h | ⟨rfl, hxx⟩
  · have hcast : ((p' + q + 1 : ℕ) : Ordinal) = ((p' + q : ℕ) : Ordinal) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have h1 : ω ^ c * (p' + q : ℕ) + (x' ♯ y) < ω ^ c * (p' + q + 1 : ℕ) := by
      rw [hcast, mul_add, mul_one]
      exact (add_lt_add_iff_left _).2 (hIH _ _ hx' hy)
    have h2 : ω ^ c * (p' + q + 1 : ℕ) ≤ ω ^ c * (p + q : ℕ) :=
      mul_le_mul_right (Nat.cast_le.2 (by omega)) _
    exact hu.trans_lt (h1.trans_le (h2.trans le_self_add))
  · exact hu.trans_lt ((add_lt_add_iff_left _).2 (nadd_lt_nadd_right hxx y))

/-- Every ordinal below `ω ^ c * (p + 1)` is of the form `ω ^ c * p' + x'` with `p' ≤ p` a natural
number and `x' < ω ^ c`. -/
theorem decomp (c : Ordinal) (p : ℕ) (A' : Ordinal) (h : A' < ω ^ c * (p + 1 : ℕ)) :
    ∃ p' : ℕ, ∃ x' : Ordinal, p' ≤ p ∧ x' < ω ^ c ∧ A' = ω ^ c * p' + x' := by
  have hne : (ω : Ordinal) ^ c ≠ 0 := (opow_pos c omega0_pos).ne'
  have hdiv : A' / ω ^ c < ((p + 1 : ℕ) : Ordinal) := (Ordinal.div_lt hne).2 h
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 (hdiv.trans (nat_lt_omega0 _))
  refine ⟨n, A' % ω ^ c, ?_, Ordinal.mod_lt _ hne, ?_⟩
  · have h' : ((n : ℕ) : Ordinal) < ((p + 1 : ℕ) : Ordinal) := hn ▸ hdiv
    have := Nat.cast_lt.1 h'
    omega
  · rw [← hn]; exact (Ordinal.div_add_mod _ _).symm

/-- Natural addition adds the leading coefficients: an upper bound version, assuming closure of
`ω ^ c` under natural addition. -/
theorem key (c : Ordinal) (hIH : ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c → x ♯ y < ω ^ c) :
    ∀ A B : Ordinal, ∀ p q : ℕ, ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c →
      A = ω ^ c * p + x → B = ω ^ c * q + y → A ♯ B ≤ ω ^ c * (p + q : ℕ) + (x ♯ y) := by
  intro A
  induction A using Ordinal.induction with
  | _ A IHA =>
    intro B
    induction B using Ordinal.induction with
    | _ B IHB =>
      intro p q x y hx hy hA hB
      have hAlt : A < ω ^ c * (p + 1 : ℕ) := by
        rw [hA, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        exact (add_lt_add_iff_left _).2 hx
      have hBlt : B < ω ^ c * (q + 1 : ℕ) := by
        rw [hB, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        exact (add_lt_add_iff_left _).2 hy
      rw [nadd_le_iff]
      constructor
      · intro A' hA'
        obtain ⟨p', x', hp', hx', rfl⟩ := decomp c p A' (hA'.trans hAlt)
        have hub := IHA _ hA' B p' q x' y hx' hy rfl hB
        refine bound_lt c hIH p' p q x' x y _ hx' hy hub ?_
        rcases lt_or_eq_of_le hp' with h | rfl
        · exact Or.inl h
        · refine Or.inr ⟨rfl, ?_⟩
          rw [hA] at hA'
          exact (add_lt_add_iff_left _).1 hA'
      · intro B' hB'
        obtain ⟨q', y', hq', hy', rfl⟩ := decomp c q B' (hB'.trans hBlt)
        have hub := IHB _ hB' p q' x y' hx hy' hA rfl
        rw [nadd_comm A _, nadd_comm x y', Nat.add_comm p q'] at hub
        rw [nadd_comm A _, nadd_comm x y, Nat.add_comm p q]
        refine bound_lt c hIH q' q p y' y x _ hy' hx hub ?_
        rcases lt_or_eq_of_le hq' with h | rfl
        · exact Or.inl h
        · refine Or.inr ⟨rfl, ?_⟩
          rw [hB] at hB'
          exact (add_lt_add_iff_left _).1 hB'

/-- Assuming `ω ^ c` is closed under natural addition, natural addition adds the multiplicities of
`ω ^ c`. -/
theorem nadd_lt_mul_nat (c : Ordinal)
    (hIH : ∀ x y : Ordinal, x < ω ^ c → y < ω ^ c → x ♯ y < ω ^ c) (m n : ℕ) (a b : Ordinal)
    (ha : a < ω ^ c * m) (hb : b < ω ^ c * n) : a ♯ b < ω ^ c * (m + n : ℕ) := by
  match m, n with
  | 0, _ => simp at ha
  | _, 0 => simp at hb
  | (m + 1), (n + 1) =>
    obtain ⟨p, x, hp, hx, rfl⟩ := decomp c m a ha
    obtain ⟨q, y, hq, hy, rfl⟩ := decomp c n b hb
    have h1 := key c hIH _ _ p q x y hx hy rfl rfl
    have h2 : ω ^ c * (p + q : ℕ) + (x ♯ y) < ω ^ c * (p + q + 1 : ℕ) := by
      rw [Nat.cast_add (p + q) 1, Nat.cast_one, mul_add, mul_one]
      exact (add_lt_add_iff_left _).2 (hIH _ _ hx hy)
    have h3 : ω ^ c * (p + q + 1 : ℕ) ≤ ω ^ c * (m + 1 + (n + 1) : ℕ) :=
      mul_le_mul_right (Nat.cast_le.2 (by omega)) _
    exact (h1.trans_lt h2).trans_le h3

/-- **Powers of `ω` are closed under natural (Hessenberg) addition.** -/
theorem nadd_lt_opow (b : Ordinal) :
    ∀ a₁ a₂ : Ordinal, a₁ < ω ^ b → a₂ < ω ^ b → a₁ ♯ a₂ < ω ^ b := by
  induction b using Ordinal.induction with
  | _ b IH =>
    intro a₁ a₂ h₁ h₂
    rcases eq_or_ne b 0 with rfl | hb
    · rw [opow_zero, lt_one_iff_zero] at h₁ h₂
      subst h₁; subst h₂
      simp
    · obtain ⟨c₁, hc₁, n₁, hn₁⟩ := (lt_omega0_opow hb).1 h₁
      obtain ⟨c₂, hc₂, n₂, hn₂⟩ := (lt_omega0_opow hb).1 h₂
      set c := max c₁ c₂ with hc
      set N := max n₁ n₂ with hN
      have hcb : c < b := max_lt hc₁ hc₂
      have hle₁ : ω ^ c₁ * (n₁ : Ordinal) ≤ ω ^ c * (N : Ordinal) :=
        mul_le_mul' (opow_le_opow_right omega0_pos (le_max_left _ _))
          (Nat.cast_le.2 (le_max_left _ _))
      have hle₂ : ω ^ c₂ * (n₂ : Ordinal) ≤ ω ^ c * (N : Ordinal) :=
        mul_le_mul' (opow_le_opow_right omega0_pos (le_max_right _ _))
          (Nat.cast_le.2 (le_max_right _ _))
      have h := nadd_lt_mul_nat c (fun x y hx hy => IH c hcb x y hx hy) N N a₁ a₂
        (hn₁.trans_le hle₁) (hn₂.trans_le hle₂)
      exact h.trans (omega0_opow_mul_nat_lt hcb _)

end KirbyParis

/-! ### Hydras -/

/-- A hydra: a finite rooted tree, given by the list of subtrees hanging from its root.  The list
is only a presentation: all notions below are invariant under permuting the children. -/
inductive Hydra where
  | node : List Hydra → Hydra
deriving Inhabited

namespace Hydra

-- `ord` : the ordinal (below `ε₀`) attached to a hydra, and `ordList`, the ordinal attached to a
-- list of hydras: `ord (node [h₁, …, hₖ]) = ω ^ ord h₁ ♯ ⋯ ♯ ω ^ ord hₖ`, using natural
-- (Hessenberg) addition, so that it does not depend on the order of the children.
mutual
/-- The ordinal (below `ε₀`) attached to a hydra:
`ord (node [h₁, …, hₖ]) = ω ^ ord h₁ ♯ ⋯ ♯ ω ^ ord hₖ`, using natural (Hessenberg) addition, so
that it does not depend on the order of the children. -/
noncomputable def ord : Hydra → Ordinal.{0}
  | .node l => ordList l

/-- The ordinal attached to a list of hydras, see `Hydra.ord`. -/
noncomputable def ordList : List Hydra → Ordinal.{0}
  | [] => 0
  | h :: t => (ω ^ ord h) ♯ ordList t
end

@[simp] theorem ord_node (l : List Hydra) : ord (node l) = ordList l := rfl

@[simp] theorem ordList_nil : ordList [] = 0 := rfl

@[simp] theorem ordList_cons (h : Hydra) (t : List Hydra) :
    ordList (h :: t) = (ω ^ ord h) ♯ ordList t := rfl

theorem ordList_append (l₁ l₂ : List Hydra) :
    ordList (l₁ ++ l₂) = ordList l₁ ♯ ordList l₂ := by
  induction l₁ with
  | nil => simp
  | cons h t ih => simp [ih, nadd_assoc]

theorem ordList_perm {l₁ l₂ : List Hydra} (h : l₁.Perm l₂) : ordList l₁ = ordList l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp [nadd_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Any number of copies of a single hydra `h` together have ordinal `< ω ^ (ord h + 1)`. -/
theorem ordList_replicate_lt (h : Hydra) (k : ℕ) :
    ordList (List.replicate k h) < ω ^ Order.succ (ord h) := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, ordList_nil]
    exact opow_pos _ omega0_pos
  | succ k ih =>
    rw [List.replicate_succ, ordList_cons]
    refine KirbyParis.nadd_lt_opow _ _ _ ?_ ih
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (Order.lt_succ _)

/-- `Step n a b`: one move of the hydra game performed *strictly inside* `a`; that is, the chopped
leaf sits at depth at least two in `a`, so that its grandparent is a node of `a` and the
duplication of the parent (creating `n` extra copies) takes place inside `a`. -/
inductive Step (n : ℕ) : Hydra → Hydra → Prop
  | /-- The chopped leaf is at depth two: its parent `node pl` (where the children `pl` of the
    parent consist of the chopped leaf `node []` together with `cs`) is a child of the root,
    which is therefore the grandparent; after removing the leaf, the parent becomes `node cs`, and
    `n` extra copies of it are attached to the root. -/
    copy {l rest cs pl : List Hydra} (h : l.Perm (node pl :: rest))
      (hp : pl.Perm (node [] :: cs)) :
      Step n (node l) (node (List.replicate (n + 1) (node cs) ++ rest))
  | /-- The move takes place inside one of the children. -/
    cong {l rest : List Hydra} {a b : Hydra} (h : l.Perm (a :: rest)) :
      Step n a b → Step n (node l) (node (b :: rest))

/-- `Move n a b`: `b` is obtained from the hydra `a` by one move of the Kirby–Paris game with
growth rate `n`: Hercules chops off a head (a leaf) of `a`; if that leaf had a grandparent, then
`n` extra copies of the parent subtree (with the leaf already removed) are grown at the
grandparent; if the leaf was a child of the root, it simply disappears. -/
inductive Move (n : ℕ) : Hydra → Hydra → Prop
  | /-- Chopping a head attached directly to the root: nothing regrows. -/
    chop {l rest : List Hydra} (h : l.Perm (node [] :: rest)) : Move n (node l) (node rest)
  | /-- Chopping a head at depth at least two: the growth happens at its grandparent, which is a
    node of the hydra. -/
    ofStep {a b : Hydra} : Step n a b → Move n a b

/-- Every move strictly inside a hydra decreases its ordinal. -/
theorem Step.ord_lt {n : ℕ} {a b : Hydra} (hab : Step n a b) : ord b < ord a := by
  induction hab with
  | @copy l rest cs pl h hp =>
    rw [ord_node, ord_node, ordList_perm h, ordList_cons, ordList_append]
    refine nadd_lt_nadd_right ?_ _
    have hord : ord (node pl) = Order.succ (ord (node cs)) := by
      rw [ord_node, ordList_perm hp, ordList_cons, ord_node, ord_node, ordList_nil, opow_zero,
        nadd_comm, nadd_one]
    rw [hord]
    exact ordList_replicate_lt (node cs) (n + 1)
  | cong h _ ih =>
    rw [ord_node, ord_node, ordList_perm h, ordList_cons, ordList_cons]
    exact nadd_lt_nadd_right ((opow_lt_opow_iff_right one_lt_omega0).2 ih) _

/-- **Every move of the hydra game strictly decreases the ordinal of the hydra.** -/
theorem Move.ord_lt {n : ℕ} {a b : Hydra} (hab : Move n a b) : ord b < ord a := by
  cases hab with
  | @chop l rest h =>
    rw [ord_node, ord_node, ordList_perm h, ordList_cons, ord_node, ordList_nil, opow_zero,
      nadd_comm, nadd_one]
    exact Order.lt_succ _
  | ofStep hs => exact hs.ord_lt

/-- Every hydra other than the dead hydra `node []` admits a legal move: the game only stops when
the hydra is dead. -/
theorem exists_step_or_leaf (n : ℕ) (l : List Hydra) (hl : l ≠ []) :
    (∃ cs, l.Perm (node [] :: cs)) ∨ ∃ b, Step n (node l) b := by
  match l with
  | [] => exact absurd rfl hl
  | (node cs) :: rest =>
    match cs with
    | [] => exact Or.inl ⟨rest, List.Perm.refl _⟩
    | c :: cs' =>
      rcases exists_step_or_leaf n (c :: cs') (by simp) with ⟨cs₂, hperm⟩ | ⟨b, hb⟩
      · exact Or.inr ⟨_, Step.copy (List.Perm.refl _) hperm⟩
      · exact Or.inr ⟨_, Step.cong (List.Perm.refl _) hb⟩
termination_by sizeOf l

/-- Every live hydra admits a legal move. -/
theorem exists_move (n : ℕ) {h : Hydra} (hh : h ≠ node []) : ∃ b, Move n h b := by
  match h with
  | node l =>
    have hl : l ≠ [] := fun hl => hh (by rw [hl])
    rcases exists_step_or_leaf n l hl with ⟨cs, hperm⟩ | ⟨b, hb⟩
    · exact ⟨node cs, Move.chop hperm⟩
    · exact ⟨b, Move.ofStep hb⟩

/-- The one-move relation of the hydra game is well founded (for a fixed growth rate). -/
theorem move_wellFounded (n : ℕ) : WellFounded (fun b a => Move n a b) :=
  Subrelation.wf (fun h => h.ord_lt) (InvImage.wf ord Ordinal.lt_wf)

/-! ### Sanity checks -/

example : ord (node []) = 0 := rfl

example : ord (node [node []]) = 1 := by simp [ord, ordList]

/-- Chopping a head attached to the root: it simply disappears. -/
example : Move 5 (node [node [], node [node []]]) (node [node [node []]]) :=
  Move.chop (List.Perm.refl _)

/-- Chopping the top of a path of length two with growth rate `2`: the parent (now a bare head)
is triplicated at the root. -/
example : Move 2 (node [node [node []]]) (node [node [], node [], node []]) :=
  Move.ofStep (Step.copy (List.Perm.refl _) (List.Perm.refl _))

/-- The hydra obtained after `N` moves of the strategy `σ`, starting from `h₀`. -/
def play (σ : ℕ → Hydra → Hydra) (h₀ : Hydra) : ℕ → Hydra
  | 0 => h₀
  | N + 1 => σ N (play σ h₀ N)

end Hydra

namespace Frontier

open Hydra

/-- **Kirby–Paris hydra theorem.**

1. There is no infinite play of the hydra game: for any sequence of hydras `f` and any sequence of
   growth rates `k`, it is impossible that `f (i+1)` results from `f i` by a legal move for all
   `i`.
2. Consequently every strategy `σ` (which, from any hydra other than the dead hydra `node []`,
   plays a legal move) kills the hydra after finitely many steps.

This is the Kirby–Paris theorem, whose statement is not provable in Peano arithmetic; the proof
here is the standard ordinal argument, carried out in ZFC via `Hydra.ord`. -/
theorem Hydra_Kirby_Paris :
    (∀ (f : ℕ → Hydra) (k : ℕ → ℕ), ¬ ∀ i, Move (k i) (f i) (f (i + 1))) ∧
    (∀ (σ : ℕ → Hydra → Hydra), (∀ i h, h ≠ node [] → Move i h (σ i h)) →
      ∀ h₀ : Hydra, ∃ N, play σ h₀ N = node []) := by
  have no_infinite : ∀ (f : ℕ → Hydra) (k : ℕ → ℕ), ¬ ∀ i, Move (k i) (f i) (f (i + 1)) := by
    intro f k hf
    have hdec : ∀ i, ord (f (i + 1)) < ord (f i) := fun i => (hf i).ord_lt
    obtain ⟨m, ⟨i, hi⟩, hmin⟩ :=
      Ordinal.lt_wf.has_min (Set.range fun i => ord (f i)) ⟨ord (f 0), 0, rfl⟩
    exact hmin (ord (f (i + 1))) ⟨i + 1, rfl⟩ (hi ▸ hdec i)
  refine ⟨no_infinite, ?_⟩
  intro σ hσ h₀
  by_contra hN
  push_neg at hN
  exact no_infinite (play σ h₀) id fun i => hσ i _ (hN i)

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

