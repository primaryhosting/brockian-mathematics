/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/
theorem div_mod_lt_of_lt {P a b : Ordinal} (hP : P ≠ 0) (h : a < b) :
    a / P < b / P ∨ (a / P = b / P ∧ a % P < b % P) := by
  rcases lt_trichotomy (a / P) (b / P) with h₁ | h₁ | h₁
  · exact Or.inl h₁
  · refine Or.inr ⟨h₁, ?_⟩
    have key : P * (a / P) + a % P < P * (a / P) + b % P := by
      rw [Ordinal.div_add_mod a P, h₁, Ordinal.div_add_mod b P]
      exact h
    exact lt_of_add_lt_add_left key
  · exfalso
    have h2 : b < P * (a / P) := by
      calc b = P * (b / P) + b % P := (Ordinal.div_add_mod b P).symm
        _ < P * (b / P) + P := by
            exact add_lt_add_right (Ordinal.mod_lt b hP) _
        _ = P * (b / P + 1) := by rw [mul_add_one]
        _ ≤ P * (a / P) := by
            exact mul_le_mul_right (Order.add_one_le_iff.2 h₁) P
    have h3 : P * (a / P) ≤ a := Ordinal.mul_div_le a P
    exact absurd (h2.trans_le h3) (not_lt_of_gt h)

/-- If `ω ^ δ` is closed under natural addition, then the natural sum of two ordinals
below `ω ^ δ * ω` is bounded by the expected quotient/remainder expression. -/
theorem nadd_le_div_mod (δ : Ordinal)
    (IH : ∀ x y : Ordinal, x < ω ^ δ → y < ω ^ δ → x ♯ y < ω ^ δ) :
    ∀ a b : Ordinal, a < ω ^ δ * ω → b < ω ^ δ * ω →
      a ♯ b ≤ ω ^ δ * (a / ω ^ δ + b / ω ^ δ) + (a % ω ^ δ ♯ b % ω ^ δ) := by
  have hP : (ω : Ordinal) ^ δ ≠ 0 := (Ordinal.opow_pos δ omega0_pos).ne'
  intro a
  induction a using Ordinal.induction with
  | _ a IHa =>
    intro b
    induction b using Ordinal.induction with
    | _ b IHb =>
      intro ha hb
      set P : Ordinal := ω ^ δ with hPdef
      have hqa : a / P < ω := (Ordinal.div_lt hP).2 ha
      have hqb : b / P < ω := (Ordinal.div_lt hP).2 hb
      have hra : a % P < P := Ordinal.mod_lt a hP
      have hrb : b % P < P := Ordinal.mod_lt b hP
      rw [nadd_le_iff]
      constructor
      · intro a' ha'
        have ha'ω : a' < P * ω := ha'.trans ha
        have hstep := IHa a' ha' b ha'ω hb
        have hra' : a' % P < P := Ordinal.mod_lt a' hP
        rcases div_mod_lt_of_lt hP ha' with hq | ⟨hq, hr⟩
        · have h1 : ω ^ δ * (a' / P + b / P) + (a' % P ♯ b % P)
              < P * (a' / P + b / P + 1) := by
            rw [mul_add_one]
            exact add_lt_add_right (IH _ _ hra' hrb) _
          have h2 : P * (a' / P + b / P + 1) ≤ P * (a / P + b / P) := by
            refine mul_le_mul_right ?_ P
            rw [Order.add_one_le_iff]
            have hqa' : a' / P < ω := (Ordinal.div_lt hP).2 ha'ω
            obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
            obtain ⟨na', hna'⟩ := Ordinal.lt_omega0.1 hqa'
            obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
            have hlt : na' < na := by
              have h' : (na' : Ordinal) < (na : Ordinal) := by rw [← hna', ← hna]; exact hq
              exact_mod_cast h'
            rw [hna, hna', hnb, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_lt]
            exact Nat.add_lt_add_right hlt nb
          calc a' ♯ b ≤ ω ^ δ * (a' / P + b / P) + (a' % P ♯ b % P) := hstep
            _ < P * (a' / P + b / P + 1) := h1
            _ ≤ P * (a / P + b / P) := h2
            _ ≤ P * (a / P + b / P) + (a % P ♯ b % P) := le_self_add
        · calc a' ♯ b ≤ ω ^ δ * (a' / P + b / P) + (a' % P ♯ b % P) := hstep
            _ = P * (a / P + b / P) + (a' % P ♯ b % P) := by rw [hq]
            _ < P * (a / P + b / P) + (a % P ♯ b % P) :=
                add_lt_add_right (nadd_lt_nadd_right hr _) _
      · intro b' hb'
        have hb'ω : b' < P * ω := hb'.trans hb
        have hstep := IHb b' hb' ha hb'ω
        have hrb' : b' % P < P := Ordinal.mod_lt b' hP
        rcases div_mod_lt_of_lt hP hb' with hq | ⟨hq, hr⟩
        · have h1 : ω ^ δ * (a / P + b' / P) + (a % P ♯ b' % P)
              < P * (a / P + b' / P + 1) := by
            rw [mul_add_one]
            exact add_lt_add_right (IH _ _ hra hrb') _
          have h2 : P * (a / P + b' / P + 1) ≤ P * (a / P + b / P) := by
            refine mul_le_mul_right ?_ P
            rw [Order.add_one_le_iff]
            have hqb' : b' / P < ω := (Ordinal.div_lt hP).2 hb'ω
            obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
            obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
            obtain ⟨nb', hnb'⟩ := Ordinal.lt_omega0.1 hqb'
            have hlt : nb' < nb := by
              have h' : (nb' : Ordinal) < (nb : Ordinal) := by rw [← hnb', ← hnb]; exact hq
              exact_mod_cast h'
            rw [hna, hnb, hnb', ← Nat.cast_add, ← Nat.cast_add, Nat.cast_lt]
            exact Nat.add_lt_add_left hlt na
          calc a ♯ b' ≤ ω ^ δ * (a / P + b' / P) + (a % P ♯ b' % P) := hstep
            _ < P * (a / P + b' / P + 1) := h1
            _ ≤ P * (a / P + b / P) := h2
            _ ≤ P * (a / P + b / P) + (a % P ♯ b % P) := le_self_add
        · calc a ♯ b' ≤ ω ^ δ * (a / P + b' / P) + (a % P ♯ b' % P) := hstep
            _ = P * (a / P + b / P) + (a % P ♯ b' % P) := by rw [hq]
            _ < P * (a / P + b / P) + (a % P ♯ b % P) :=
                add_lt_add_right (nadd_lt_nadd_left hr _) _

/-- The successor step of additive principality. -/
theorem nadd_lt_opow_succ (δ : Ordinal)
    (IH : ∀ x y : Ordinal, x < ω ^ δ → y < ω ^ δ → x ♯ y < ω ^ δ) :
    ∀ a b : Ordinal, a < ω ^ (δ + 1) → b < ω ^ (δ + 1) → a ♯ b < ω ^ (δ + 1) := by
  have hP : (ω : Ordinal) ^ δ ≠ 0 := (Ordinal.opow_pos δ omega0_pos).ne'
  intro a b ha hb
  rw [Ordinal.opow_add, Ordinal.opow_one] at ha hb ⊢
  set P : Ordinal := ω ^ δ with hPdef
  have hqa : a / P < ω := (Ordinal.div_lt hP).2 ha
  have hqb : b / P < ω := (Ordinal.div_lt hP).2 hb
  have hra : a % P < P := Ordinal.mod_lt a hP
  have hrb : b % P < P := Ordinal.mod_lt b hP
  have hmain := nadd_le_div_mod δ IH a b ha hb
  have h1 : P * (a / P + b / P) + (a % P ♯ b % P) < P * (a / P + b / P + 1) := by
    rw [mul_add_one]
    exact add_lt_add_right (IH _ _ hra hrb) _
  have h2 : P * (a / P + b / P + 1) < P * ω := by
    refine (mul_lt_mul_iff_of_pos_left (Ordinal.opow_pos δ omega0_pos)).2 ?_
    obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
    obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
    rw [hna, hnb, ← Nat.cast_add, ← Nat.cast_one, ← Nat.cast_add]
    exact Ordinal.nat_lt_omega0 (na + nb + 1)
  exact lt_of_le_of_lt hmain (h1.trans h2)

/-- **Additive principality of `ω ^ γ`**: the set of ordinals below `ω ^ γ` is closed
under the natural (Hessenberg) sum. -/
theorem nadd_lt_opow {γ a b : Ordinal} (ha : a < ω ^ γ) (hb : b < ω ^ γ) : a ♯ b < ω ^ γ := by
  induction γ using Ordinal.induction generalizing a b with
  | _ γ IH =>
    rcases eq_or_ne a 0 with rfl | ha0
    · rwa [zero_nadd]
    rcases eq_or_ne b 0 with rfl | hb0
    · rwa [nadd_zero]
    have h1 : Ordinal.log ω a < γ := (Ordinal.lt_opow_iff_log_lt one_lt_omega0 ha0).1 ha
    have h2 : Ordinal.log ω b < γ := (Ordinal.lt_opow_iff_log_lt one_lt_omega0 hb0).1 hb
    set δ : Ordinal := max (Ordinal.log ω a) (Ordinal.log ω b) with hδ
    have hδγ : δ < γ := max_lt h1 h2
    have ha' : a < ω ^ (δ + 1) :=
      (Ordinal.lt_opow_iff_log_lt one_lt_omega0 ha0).2 (by
        simp [hδ])
    have hb' : b < ω ^ (δ + 1) :=
      (Ordinal.lt_opow_iff_log_lt one_lt_omega0 hb0).2 (by
        simp [hδ])
    have hIH : ∀ x y : Ordinal, x < ω ^ δ → y < ω ^ δ → x ♯ y < ω ^ δ :=
      fun x y hx hy => IH δ hδγ hx hy
    have := nadd_lt_opow_succ δ hIH a b ha' hb'
    exact this.trans_le (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_iff.2 hδγ))

end Frontier

import Mathlib
import RequestProject.OrdinalNaddOpow

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Kirby–Paris hydra theorem

A *hydra* is a finite rooted tree, encoded as `Hydra.node : List Hydra → Hydra`.
Hercules chops off a *head* (a leaf) of the hydra; if the head was attached to the root
the hydra simply loses it, and otherwise the hydra grows `n` fresh copies of the subtree
hanging below the head's grandparent-child (i.e. below the head's parent, after the head
has been removed), attached to the head's grandparent.  The number `n` of copies is chosen
freely by the hydra at each round.

`Frontier.HydraStep n h h'` is the relation "`h'` is obtained from `h` by one round in which
the hydra grows `n` copies".  The theorem `Frontier.Hydra_Kirby_Paris` states that no infinite
battle exists: whatever heads Hercules chooses and whatever regrowth numbers the hydra chooses,
the game terminates.

The proof assigns to each hydra an ordinal below `ε₀`:
`ord (node [t₁,…,t_k]) = ω ^ ord t₁ ♯ ⋯ ♯ ω ^ ord t_k` (Hessenberg natural sum), and shows that
every round strictly decreases this ordinal.
-/

open Ordinal NaturalOps Order

namespace Frontier

/-- A hydra: a finite rooted tree, given by the list of subtrees hanging from its root. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/- The ordinal measure of a hydra, and of a list of hydras, defined by mutual recursion:
`ord (node l) = ordList l` and `ordList (t :: ts) = ω ^ ord t ♯ ordList ts`. -/
mutual

/-- The ordinal measure of a hydra: `ord (node [t₁,…,t_k]) = ω ^ ord t₁ ♯ ⋯ ♯ ω ^ ord t_k`. -/
noncomputable def ord : Hydra → Ordinal.{0}
  | .node l => ordList l

/-- The ordinal measure of a list of hydras: the natural sum of `ω ^ ord tᵢ`. -/
noncomputable def ordList : List Hydra → Ordinal.{0}
  | [] => 0
  | t :: ts => (ω ^ ord t) ♯ ordList ts

end

@[simp] theorem ord_node (l : List Hydra) : ord (.node l) = ordList l := by
  rw [ord]

@[simp] theorem ordList_nil : ordList [] = 0 := by
  rw [ordList]

@[simp] theorem ordList_cons (t : Hydra) (ts : List Hydra) :
    ordList (t :: ts) = (ω ^ ord t) ♯ ordList ts := by
  rw [ordList]

theorem ordList_append (l₁ l₂ : List Hydra) :
    ordList (l₁ ++ l₂) = ordList l₁ ♯ ordList l₂ := by
  induction l₁ with
  | nil => simp
  | cons t ts ih => simp [ih, nadd_assoc]

/-- If all members of a list have ordinal measure `< γ`, the list's measure is `< ω ^ γ`. -/
theorem ordList_lt_opow {l : List Hydra} {γ : Ordinal} (h : ∀ t ∈ l, ord t < γ) :
    ordList l < ω ^ γ := by
  induction l with
  | nil => simpa using Ordinal.opow_pos γ omega0_pos
  | cons t ts ih =>
      rw [ordList_cons]
      refine nadd_lt_opow ?_ (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
      exact (Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 (h t List.mem_cons_self)

end Hydra

/-- One round of the hydra game, in which the hydra regrows `n` copies.

* `chop`: Hercules removes a head attached directly to the root; nothing regrows.
* `copy`: Hercules removes a head at distance two from the root; the root then grows `n`
  copies of the head's parent, with the head removed.
* `ctx`: the round takes place inside one of the subtrees hanging from the root. -/
inductive HydraStep : ℕ → Hydra → Hydra → Prop
  | chop (n : ℕ) (l₁ l₂ : List Hydra) :
      HydraStep n (.node (l₁ ++ .node [] :: l₂)) (.node (l₁ ++ l₂))
  | copy (n : ℕ) (l₁ l₂ m₁ m₂ : List Hydra) :
      HydraStep n (.node (l₁ ++ .node (m₁ ++ .node [] :: m₂) :: l₂))
        (.node (l₁ ++ List.replicate n (.node (m₁ ++ m₂)) ++ l₂))
  | ctx (n : ℕ) (l₁ l₂ : List Hydra) (t t' : Hydra) :
      HydraStep n t t' → HydraStep n (.node (l₁ ++ t :: l₂)) (.node (l₁ ++ t' :: l₂))

open Hydra

/-- Removing a head from the children of a node decreases its measure by exactly one. -/
theorem ord_node_chop_head (m₁ m₂ : List Hydra) :
    ord (.node (m₁ ++ .node [] :: m₂)) = succ (ord (.node (m₁ ++ m₂))) := by
  simp only [ord_node, ordList_append, ordList_cons, ordList_nil, Ordinal.opow_zero]
  rw [one_nadd, nadd_succ]

/-- Every round of the hydra game strictly decreases the ordinal measure. -/
theorem HydraStep.ord_lt {n : ℕ} {h h' : Hydra} (hs : HydraStep n h h') : ord h' < ord h := by
  induction hs with
  | chop l₁ l₂ =>
      simp only [ord_node, ordList_append, ordList_cons, ordList_nil, Ordinal.opow_zero]
      exact nadd_lt_nadd_left (by rw [one_nadd]; exact lt_succ _) _
  | copy l₁ l₂ m₁ m₂ =>
      have hsucc := ord_node_chop_head m₁ m₂
      have hkey : ordList (List.replicate n (Hydra.node (m₁ ++ m₂)))
          < ω ^ ord (Hydra.node (m₁ ++ .node [] :: m₂)) := by
        refine ordList_lt_opow ?_
        intro t ht
        rw [List.eq_of_mem_replicate ht, hsucc]
        exact lt_succ _
      simp only [ord_node, ordList_append, ordList_cons, nadd_assoc] at hkey ⊢
      exact nadd_lt_nadd_left (nadd_lt_nadd_right hkey _) _
  | ctx l₁ l₂ t t' _ ih =>
      simp only [ord_node, ordList_append, ordList_cons]
      refine nadd_lt_nadd_left (nadd_lt_nadd_right ?_ _) _
      exact (Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 ih

/-- The hydra game relation is well founded. -/
theorem hydraStep_wellFounded :
    WellFounded (fun h' h : Hydra => ∃ n : ℕ, HydraStep n h h') := by
  refine Subrelation.wf ?_ (InvImage.wf ord Ordinal.lt_wf)
  rintro h' h ⟨n, hs⟩
  exact hs.ord_lt

/-- **Kirby–Paris hydra theorem.**  Every hydra game terminates, for every strategy of
Hercules and every regrowth behaviour of the hydra: there is no infinite sequence of hydras
`f 0, f 1, f 2, …` in which each `f (k+1)` arises from `f k` by a legal round of the game
(the hydra growing `c k` copies at round `k`). -/
theorem Hydra_Kirby_Paris (f : ℕ → Hydra) (c : ℕ → ℕ) :
    ¬ ∀ k : ℕ, HydraStep (c k) (f k) (f (k + 1)) := by
  intro hplay
  have hdec : ∀ k : ℕ, ord (f (k + 1)) < ord (f k) := fun k => (hplay k).ord_lt
  exact (RelEmbedding.natGT (fun k => ord (f k)) hdec).not_wellFounded Ordinal.lt_wf

/-- Sanity check: the game relation is inhabited.  From the hydra with a single branch of
length two, chopping its unique head makes the root grow two copies of the (now headless)
branch. -/
example : HydraStep 2 (.node [.node [.node []]]) (.node [.node [], .node []]) := by
  simpa using HydraStep.copy 2 [] [] [] []

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

