import Mathlib

/-!
# A formal model of a privilege-isolation engine

We model an *isolation policy* on a finite set of compartments `C` as a boolean
edge relation `edge : C → C → Bool`, where `edge a b = true` means that a
principal running in compartment `a` is permitted to influence / reach
compartment `b` (a channel that is *not* isolated).

The *ground truth* semantics of privilege escape is reachability
(`PCA.Isolation.Policy.Reach`, the reflexive transitive closure of `edge`).

The *engine* is a concrete computation: iterate a one-step expansion
`Policy.step` starting from `{s}`, `Fintype.card C` times
(`Policy.escape`).  We prove:

* `Policy.escape_sound`    – the engine never over-approximates,
* `Policy.escape_complete` – the engine never under-approximates,
* `Policy.mem_escape_iff`  – hence the engine decides reachability exactly,
* `PCA.Isolation.priv_escape_monotone` – weakening the isolation (adding
  permitted edges) can only increase the set of privileges reachable from a
  compartment.
-/

namespace PCA.Isolation

open Finset

/-- An isolation policy on a set of compartments `C`: `edge a b` says that
compartment `a` may influence compartment `b`. -/
structure Policy (C : Type*) where
  /-- `edge a b = true` means the channel from `a` to `b` is *not* isolated. -/
  edge : C → C → Bool

variable {C A : Type*} [Fintype C] [DecidableEq C]

/-- Privilege escape, semantically: `Reach P s d` iff `d` is reachable from `s`
along permitted channels. -/
def Policy.Reach (P : Policy C) : C → C → Prop :=
  Relation.ReflTransGen (fun a b => P.edge a b = true)

/-- One expansion step of the isolation engine. -/
def Policy.step (P : Policy C) (S : Finset C) : Finset C :=
  S ∪ S.biUnion (fun c => Finset.univ.filter (fun d => P.edge c d = true))

/-- The engine's frontier after `k` expansion steps starting from `{s}`. -/
def Policy.iter (P : Policy C) (s : C) : ℕ → Finset C
  | 0 => {s}
  | k + 1 => P.step (P.iter s k)

/-- The set of compartments the isolation engine reports as escapable from `s`. -/
def Policy.escape (P : Policy C) (s : C) : Finset C :=
  P.iter s (Fintype.card C)

/-- The privileges the engine reports as escapable from `s`, given the
privileges `priv c` held by each compartment `c`. -/
def Policy.privEscape [DecidableEq A] (P : Policy C) (priv : C → Finset A) (s : C) :
    Finset A :=
  (P.escape s).biUnion priv

/-! ### Basic properties of `step` -/

theorem Policy.mem_step {P : Policy C} {S : Finset C} {d : C} :
    d ∈ P.step S ↔ d ∈ S ∨ ∃ c ∈ S, P.edge c d = true := by
  simp [Policy.step]

theorem Policy.subset_step (P : Policy C) (S : Finset C) : S ⊆ P.step S := by
  intro x hx
  exact Policy.mem_step.2 (Or.inl hx)

theorem Policy.step_mono (P : Policy C) {S T : Finset C} (h : S ⊆ T) :
    P.step S ⊆ P.step T := by
  intro x hx
  rcases Policy.mem_step.1 hx with hx | ⟨c, hc, hcx⟩
  · exact Policy.mem_step.2 (Or.inl (h hx))
  · exact Policy.mem_step.2 (Or.inr ⟨c, h hc, hcx⟩)

/-! ### Monotonicity of the iteration -/

theorem Policy.iter_subset_succ (P : Policy C) (s : C) (k : ℕ) :
    P.iter s k ⊆ P.iter s (k + 1) :=
  P.subset_step _

theorem Policy.iter_mono (P : Policy C) (s : C) {k m : ℕ} (h : k ≤ m) :
    P.iter s k ⊆ P.iter s m := by
  induction m with
  | zero => simp_all
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · exact (ih (Nat.lt_succ_iff.1 hk)).trans (P.iter_subset_succ s n)
    · have : k = n + 1 := le_antisymm h hk
      subst this; exact Finset.Subset.refl _

theorem Policy.iter_fix (P : Policy C) (s : C) {k : ℕ}
    (hk : P.iter s k = P.iter s (k + 1)) : ∀ m, P.iter s (k + m) = P.iter s k := by
  intro m
  induction m with
  | zero => rfl
  | succ n ih =>
    show P.step (P.iter s (k + n)) = P.iter s k
    rw [ih, ← Policy.iter, ← hk]

theorem Policy.card_iter_ge (P : Policy C) (s : C) (k : ℕ)
    (h : ∀ j < k, P.iter s j ≠ P.iter s (j + 1)) : k + 1 ≤ (P.iter s k).card := by
  induction k with
  | zero => simp [Policy.iter]
  | succ n ih =>
    have hn : n + 1 ≤ (P.iter s n).card := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hss : P.iter s n ⊂ P.iter s (n + 1) :=
      Finset.ssubset_iff_subset_ne.2 ⟨P.iter_subset_succ s n, h n (Nat.lt_succ_self n)⟩
    have := Finset.card_lt_card hss
    omega

theorem Policy.exists_fix (P : Policy C) (s : C) :
    ∃ k ≤ Fintype.card C, P.iter s k = P.iter s (k + 1) := by
  by_contra hcon
  push_neg at hcon
  have h : ∀ j < Fintype.card C, P.iter s j ≠ P.iter s (j + 1) := by
    intro j hj
    exact hcon j (le_of_lt hj)
  have h1 := P.card_iter_ge s (Fintype.card C) h
  have h2 : (P.iter s (Fintype.card C)).card ≤ Fintype.card C := Finset.card_le_univ _
  omega

theorem Policy.iter_subset_escape (P : Policy C) (s : C) (j : ℕ) :
    P.iter s j ⊆ P.escape s := by
  obtain ⟨k, hkN, hk⟩ := P.exists_fix s
  have hstab : ∀ m, k ≤ m → P.iter s m = P.iter s k := by
    intro m hm
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact P.iter_fix s hk t
  rcases Nat.lt_or_ge j k with hj | hj
  · exact (P.iter_mono s (le_of_lt hj)).trans
      (by rw [Policy.escape, hstab (Fintype.card C) hkN])
  · rw [Policy.escape, hstab (Fintype.card C) hkN, hstab j hj]

/-! ### Soundness and completeness of the engine -/

theorem Policy.iter_sound (P : Policy C) (s : C) :
    ∀ (k : ℕ) {d : C}, d ∈ P.iter s k → P.Reach s d := by
  intro k
  induction k with
  | zero =>
    intro d hd
    rw [Policy.iter, Finset.mem_singleton] at hd
    subst hd
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro d hd
    rcases Policy.mem_step.1 hd with hd | ⟨c, hc, hcd⟩
    · exact ih hd
    · exact Relation.ReflTransGen.tail (ih hc) hcd

/-- **Soundness**: everything the engine reports as escapable really is
reachable along permitted channels. -/
theorem Policy.escape_sound (P : Policy C) (s : C) {d : C} (hd : d ∈ P.escape s) :
    P.Reach s d :=
  P.iter_sound s _ hd

theorem Policy.reach_mem_iter (P : Policy C) {s d : C} (h : P.Reach s d) :
    ∃ k, d ∈ P.iter s k := by
  induction h with
  | refl => exact ⟨0, Finset.mem_singleton_self s⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, Policy.mem_step.2 (Or.inr ⟨_, hk, hbc⟩)⟩

/-- **Completeness**: everything reachable along permitted channels is reported
by the engine. -/
theorem Policy.escape_complete (P : Policy C) {s d : C} (h : P.Reach s d) :
    d ∈ P.escape s := by
  obtain ⟨k, hk⟩ := P.reach_mem_iter h
  exact P.iter_subset_escape s k hk

/-- The isolation engine decides privilege escape exactly. -/
theorem Policy.mem_escape_iff (P : Policy C) (s d : C) :
    d ∈ P.escape s ↔ P.Reach s d :=
  ⟨fun h => P.escape_sound s h, fun h => P.escape_complete h⟩

theorem Policy.mem_privEscape_iff [DecidableEq A] (P : Policy C) (priv : C → Finset A)
    (s : C) (a : A) :
    a ∈ P.privEscape priv s ↔ ∃ c, P.Reach s c ∧ a ∈ priv c := by
  simp only [Policy.privEscape, Finset.mem_biUnion, P.mem_escape_iff]

/-! ### Monotonicity of privilege escape -/

omit [Fintype C] [DecidableEq C] in
theorem Policy.reach_mono {P Q : Policy C} (h : ∀ a b, P.edge a b = true → Q.edge a b = true)
    {s d : C} (hr : P.Reach s d) : Q.Reach s d :=
  Relation.ReflTransGen.mono (fun a b hab => h a b hab) hr

/-- **Privilege escape is monotone in the policy**: if every channel permitted by
`P` is also permitted by `Q` (i.e. `Q` isolates no more than `P` does), then every
privilege escapable from `s` under `P` is escapable from `s` under `Q`. -/
theorem priv_escape_monotone [DecidableEq A] {P Q : Policy C}
    (h : ∀ a b, P.edge a b = true → Q.edge a b = true) (priv : C → Finset A) (s : C) :
    P.privEscape priv s ⊆ Q.privEscape priv s := by
  intro a ha
  rw [Policy.mem_privEscape_iff] at ha ⊢
  obtain ⟨c, hc, hac⟩ := ha
  exact ⟨c, Policy.reach_mono h hc, hac⟩

end PCA.Isolation

/-! ### A sanity check that the model is non-degenerate

Three compartments `0, 1, 2` with permitted channels `0 → 1` and `1 → 2` only:
everything is escapable from `0`, while `2` is fully isolated. -/

namespace Example

/-- The chain policy `0 → 1 → 2` on three compartments. -/
def chain : PCA.Isolation.Policy (Fin 3) where
  edge a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

example : chain.escape 0 = {0, 1, 2} := by decide

example : chain.escape 2 = {2} := by decide

end Example

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

