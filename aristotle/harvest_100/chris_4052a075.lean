import Mathlib
import RequestProject.GlobalWorkspaceFixpoint

/-!
# Global Workspace Fixpoint — Mathlib interface

A restatement of `Frontier.global_workspace_fixpoint` for Mathlib's order-theoretic
hierarchy: on any finite lattice with a bottom element, a monotone (broadcast)
operator has a least fixed point, reached by finitely many iterations from `⊥`.
-/

namespace Frontier

variable {α : Type*} [Fintype α] [Lattice α] [OrderBot α]

/-- The global workspace attached to a monotone operator on a finite Mathlib lattice. -/
noncomputable def ofMonotone (f : α → α) (hf : Monotone f) : GlobalWorkspace α where
  le a b := a ≤ b
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  sup := (· ⊔ ·)
  le_sup_left := fun _ _ => le_sup_left
  le_sup_right := fun _ _ => le_sup_right
  sup_le := fun h h' => sup_le h h'
  inf := (· ⊓ ·)
  inf_le_left := fun _ _ => inf_le_left
  inf_le_right := fun _ _ => inf_le_right
  le_inf := le_inf
  bot := ⊥
  bot_le := fun _ => bot_le
  elems := Finset.univ.toList
  mem_elems := fun a => Finset.mem_toList.mpr (Finset.mem_univ a)
  bcast := f
  bcast_mono := fun h => hf h

lemma ofMonotone_iter (f : α → α) (hf : Monotone f) (n : ℕ) :
    (ofMonotone f hf).iter n = f^[n] ⊥ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [GlobalWorkspace.iter, ih, Function.iterate_succ_apply']
      rfl

/-- **Knaster–Tarski, Mathlib form.** A monotone broadcast operator on a finite lattice
with least element has a least fixed point, and it is `f^[n] ⊥` for some `n`. -/
theorem monotone_exists_isLeast_fixedPoints (f : α → α) (hf : Monotone f) :
    ∃ n : ℕ, IsLeast {a : α | f a = a} (f^[n] ⊥) := by
  obtain ⟨n, hfix, hleast⟩ := global_workspace_fixpoint (ofMonotone f hf)
  refine ⟨n, ?_, ?_⟩
  · show f (f^[n] ⊥) = f^[n] ⊥
    rw [← ofMonotone_iter f hf n]
    exact hfix
  · intro b hb
    rw [← ofMonotone_iter f hf n]
    exact hleast b hb

end Frontier

/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-- A **finite state lattice**: a finite partially ordered set `α` which is a lattice
(binary joins `sup` and meets `inf`) with a least element `bot`.  Finiteness is
recorded by a list `elems` containing every element. -/
structure StateLattice (α : Type u) where
  /-- The information ordering on workspace states. -/
  le : α → α → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  /-- Binary join (least upper bound). -/
  sup : α → α → α
  le_sup_left : ∀ a b, le a (sup a b)
  le_sup_right : ∀ a b, le b (sup a b)
  sup_le : ∀ {a b c}, le a c → le b c → le (sup a b) c
  /-- Binary meet (greatest lower bound). -/
  inf : α → α → α
  inf_le_left : ∀ a b, le (inf a b) a
  inf_le_right : ∀ a b, le (inf a b) b
  le_inf : ∀ {a b c}, le c a → le c b → le c (inf a b)
  /-- The least element: the empty workspace. -/
  bot : α
  bot_le : ∀ a, le bot a
  /-- A list of all the (finitely many) states. -/
  elems : List α
  mem_elems : ∀ a, a ∈ elems

/-- A **global workspace**: a finite state lattice together with a monotone
*broadcast operator* `bcast`, which sends the current workspace content to the
content resulting from one round of global broadcasting.  Monotonicity says that
broadcasting from a more informative state gives a more informative result. -/
structure GlobalWorkspace (α : Type u) extends StateLattice α where
  /-- The broadcast (global-workspace) operator. -/
  bcast : α → α
  bcast_mono : ∀ {a b}, le a b → le (bcast a) (bcast b)

variable {α : Type u}

/-- `m` is a *least fixed point* of the broadcast operator: it is a fixed point,
and it is below every fixed point. -/
def GlobalWorkspace.IsLeastFixpoint (W : GlobalWorkspace α) (m : α) : Prop :=
  W.bcast m = m ∧ ∀ b, W.bcast b = b → W.le m b

/-- The `n`-fold iterated broadcast, started from the empty workspace `bot`. -/
def GlobalWorkspace.iter (W : GlobalWorkspace α) : Nat → α
  | 0 => W.bot
  | n + 1 => W.bcast (W.iter n)

/-- Successive iterates are increasing. -/
theorem GlobalWorkspace.iter_le_succ (W : GlobalWorkspace α) (n : Nat) :
    W.le (W.iter n) (W.iter (n + 1)) := by
  induction n with
  | zero => exact W.bot_le _
  | succ k ih => exact W.bcast_mono ih

/-- Every iterate is below every fixed point of the broadcast operator. -/
theorem GlobalWorkspace.iter_le_of_fixed (W : GlobalWorkspace α) {b : α}
    (hb : W.bcast b = b) (n : Nat) : W.le (W.iter n) b := by
  induction n with
  | zero => exact W.bot_le _
  | succ k ih =>
      have h := W.bcast_mono ih
      rw [hb] at h
      exact h

/-- Auxiliary counting lemma: if `q` holds wherever `p` does on `l`, and some element
of `l` satisfies `q` but not `p`, then strictly more elements of `l` satisfy `q`. -/
theorem countP_lt_countP_of_witness {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      ∀ {a : α}, a ∈ l → p a = false → q a = true → l.countP p < l.countP q := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b t ih =>
      intro h a ha hp hq
      have hmono : t.countP p ≤ t.countP q :=
        List.countP_mono_left (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp ha with rfl | hat
      · simp only [hp, hq, Bool.false_eq_true, if_false, if_true]
        omega
      · have hlt := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hat hp hq
        have hstep : (if p b = true then 1 else 0) ≤ (if q b = true then 1 else 0) := by
          cases hb : p b with
          | false => simp
          | true =>
              have : q b = true := h b (List.mem_cons_self ..) hb
              simp [this]
        have h1 : (if p b = true then 1 else 0) ≤ 1 := by cases p b <;> simp
        have h2 : (if q b = true then 1 else 0) ≤ 1 := by cases q b <;> simp
        omega

open scoped Classical in
/-- The number of states below `a`; a measure of how much has been broadcast. -/
noncomputable def GlobalWorkspace.below (W : GlobalWorkspace α) (a : α) : Nat :=
  W.elems.countP (fun x => decide (W.le x a))

open scoped Classical in
/-- If an iterate is not yet stationary, the measure `below` strictly increases. -/
theorem GlobalWorkspace.below_lt_below (W : GlobalWorkspace α) {n : Nat}
    (hne : W.iter (n + 1) ≠ W.iter n) : W.below (W.iter n) < W.below (W.iter (n + 1)) := by
  refine countP_lt_countP_of_witness (a := W.iter (n + 1)) ?_ (W.mem_elems _) ?_ ?_
  · intro x _ hx
    have hx' : W.le x (W.iter n) := of_decide_eq_true hx
    exact decide_eq_true (W.le_trans hx' (W.iter_le_succ n))
  · apply decide_eq_false
    intro hle
    exact hne (W.le_antisymm hle (W.iter_le_succ n))
  · exact decide_eq_true (W.le_refl _)

/-- The measure is bounded by the number of states. -/
theorem GlobalWorkspace.below_le (W : GlobalWorkspace α) (a : α) :
    W.below a ≤ W.elems.length := by
  classical
  exact List.countP_le_length

/-- Either the broadcast iteration has already become stationary, or the measure
`below` has grown by at least `n` after `n` steps. -/
theorem GlobalWorkspace.stabilize_or_grow (W : GlobalWorkspace α) :
    ∀ n : Nat, (∃ k, W.iter (k + 1) = W.iter k) ∨ n ≤ W.below (W.iter n) := by
  intro n
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ k ih =>
      rcases ih with h | h
      · exact Or.inl h
      · rcases Classical.em (W.iter (k + 1) = W.iter k) with heq | hne
        · exact Or.inl ⟨k, heq⟩
        · have := W.below_lt_below hne
          exact Or.inr (by omega)

/-- The broadcast iteration reaches a stationary point after finitely many rounds. -/
theorem GlobalWorkspace.exists_stationary (W : GlobalWorkspace α) :
    ∃ n, W.bcast (W.iter n) = W.iter n := by
  rcases W.stabilize_or_grow (W.elems.length + 1) with ⟨k, hk⟩ | h
  · exact ⟨k, hk⟩
  · have := W.below_le (W.iter (W.elems.length + 1))
    omega

/-- **Knaster–Tarski for a global workspace.**
A monotone broadcast operator on a finite state lattice has a least fixed point,
and this least fixed point is reached after finitely many rounds of broadcasting
starting from the empty workspace `bot`. -/
theorem global_workspace_fixpoint (W : GlobalWorkspace α) :
    ∃ n : Nat, W.IsLeastFixpoint (W.iter n) := by
  obtain ⟨n, hn⟩ := W.exists_stationary
  exact ⟨n, hn, fun b hb => W.iter_le_of_fixed hb n⟩

/-- The least fixed point is unique. -/
theorem GlobalWorkspace.isLeastFixpoint_unique (W : GlobalWorkspace α) {m m' : α}
    (h : W.IsLeastFixpoint m) (h' : W.IsLeastFixpoint m') : m = m' :=
  W.le_antisymm (h.2 m' h'.1) (h'.2 m h.1)

/-- A concrete two-state global workspace (`false` = nothing broadcast, `true` = broadcast),
witnessing that the definitions above are satisfiable. -/
def boolWorkspace : GlobalWorkspace Bool where
  le a b := a = true → b = true
  le_refl := by intro a h; exact h
  le_trans := by intro a b c hab hbc h; exact hbc (hab h)
  le_antisymm := by intro a b hab hba; revert hab hba; cases a <;> cases b <;> simp
  sup a b := a || b
  le_sup_left := by intro a b h; simp [h]
  le_sup_right := by intro a b h; simp [h]
  sup_le := by intro a b c hac hbc h; revert hac hbc h; cases a <;> cases b <;> simp
  inf a b := a && b
  inf_le_left := by intro a b h; revert h; cases a <;> cases b <;> simp
  inf_le_right := by intro a b h; revert h; cases a <;> cases b <;> simp
  le_inf := by intro a b c hca hcb h; simp [hca h, hcb h]
  bot := false
  bot_le := by intro a h; simp at h
  elems := [false, true]
  mem_elems := by decide
  bcast a := a
  bcast_mono := by intro a b h; exact h

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

