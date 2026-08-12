import Mathlib

/-!
# A verified model of an isolation engine

This file formalises the abstract model underlying an *isolation engine*: a static
analysis that, given a finite object graph, decides whether the isolate can reach
an object that it does not own (an *escape*).

* `PCA.Isolation.Model` is a finite object graph: each object has a finite set of
  outgoing references (`succ`), there is a finite set of entry points (`roots`), and
  a finite set of objects `owned` by the isolate.
* `PCA.Isolation.Reachable` is the *specification*: the reflexive–transitive closure
  of the reference relation, started at the roots.
* `PCA.Isolation.escapes` is the *engine*: a terminating, decidable fixed-point
  computation (iterated frontier expansion, run for `card V + 1` rounds) which
  reports whether some object outside the ownership set is in the computed closure.

The main theorem `PCA.Isolation.null_escape_iff_unowned_reachable` states that the
engine is both sound and complete for its specification: it reports an escape if and
only if some unowned object is genuinely reachable from the roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

universe u

/-- A finite object graph together with the isolate's roots and ownership set. -/
structure Model (V : Type u) where
  /-- The references emanating from an object. -/
  succ : V → Finset V
  /-- The entry points of the isolate. -/
  roots : Finset V
  /-- The objects owned by the isolate. -/
  owned : Finset V

variable {V : Type u} [DecidableEq V] (M : Model V)

/-- The reference relation of the model: `b` is directly referenced by `a`. -/
def Edge (a b : V) : Prop := b ∈ M.succ a

/-- Specification: `v` is reachable from the isolate's roots by following references. -/
def Reachable (v : V) : Prop :=
  ∃ r ∈ M.roots, Relation.ReflTransGen (Edge M) r v

/-- One round of frontier expansion. -/
def step (s : Finset V) : Finset V := s ∪ s.biUnion M.succ

/-- The set of objects discovered after `n` rounds of expansion. -/
def frontier (n : ℕ) : Finset V := (step M)^[n] M.roots

/-- The engine's computed reachable set: expansion run to its fixed point.
`Fintype.card V + 1` rounds always suffice. -/
def closure [Fintype V] : Finset V := frontier M (Fintype.card V + 1)

/-- The objects the engine flags as escaping: discovered by the analysis, yet not
owned by the isolate. -/
def escapeSet [Fintype V] : Finset V := closure M \ M.owned

/-- The engine's verdict: `true` exactly when the escape set is non-empty. -/
def escapes [Fintype V] : Bool := decide (escapeSet M).Nonempty

/-! ### Basic properties of `step` and `frontier` -/

theorem subset_step (s : Finset V) : s ⊆ step M s := Finset.subset_union_left

theorem step_mono {s t : Finset V} (h : s ⊆ t) : step M s ⊆ step M t := by
  unfold step
  exact Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

theorem frontier_succ (n : ℕ) : frontier M (n + 1) = step M (frontier M n) :=
  Function.iterate_succ_apply' _ _ _

theorem frontier_zero : frontier M 0 = M.roots := rfl

theorem frontier_subset_succ (n : ℕ) : frontier M n ⊆ frontier M (n + 1) := by
  rw [frontier_succ]; exact subset_step M _

theorem frontier_mono {m n : ℕ} (h : m ≤ n) : frontier M m ⊆ frontier M n := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (frontier_subset_succ M k)
    · have : m = k + 1 := le_antisymm h hge
      subst this; exact Finset.Subset.refl _

/-! ### Soundness: everything the engine discovers is genuinely reachable -/

theorem reachable_of_mem_frontier {n : ℕ} {v : V} (hv : v ∈ frontier M n) :
    Reachable M v := by
  induction n generalizing v with
  | zero => exact ⟨v, hv, Relation.ReflTransGen.refl⟩
  | succ k ih =>
    rw [frontier_succ, step, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact ih hv
    · rw [Finset.mem_biUnion] at hv
      obtain ⟨a, ha, hav⟩ := hv
      obtain ⟨r, hr, hpath⟩ := ih ha
      exact ⟨r, hr, hpath.tail hav⟩

/-! ### Completeness: everything reachable is discovered in finitely many rounds -/

theorem exists_mem_frontier_of_reachable {v : V} (hv : Reachable M v) :
    ∃ n, v ∈ frontier M n := by
  obtain ⟨r, hr, hpath⟩ := hv
  induction hpath with
  | refl => exact ⟨0, hr⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [frontier_succ, step, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨_, hn, hbc⟩)

/-! ### The expansion reaches a fixed point within `card V` rounds -/

theorem frontier_stable_of_eq {n : ℕ} (h : frontier M n = frontier M (n + 1)) :
    ∀ m, n ≤ m → frontier M m = frontier M n := by
  intro m hm
  induction m with
  | zero => simp [Nat.le_zero.mp hm]
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hk : n ≤ k := Nat.lt_succ_iff.mp hlt
      rw [frontier_succ, ih hk, ← frontier_succ, ← h]
    · have : n = k + 1 := le_antisymm hm hge
      rw [this]

theorem card_frontier_ge_of_strict [Fintype V] {N : ℕ}
    (h : ∀ n ≤ N, frontier M n ≠ frontier M (n + 1)) :
    ∀ n ≤ N + 1, n ≤ (frontier M n).card := by
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hk
    have hkN : k ≤ N := by omega
    have hsub : frontier M k ⊆ frontier M (k + 1) := frontier_subset_succ M k
    have hne : frontier M k ≠ frontier M (k + 1) := h k hkN
    have hlt : (frontier M k).card < (frontier M (k + 1)).card :=
      Finset.card_lt_card (lt_of_le_of_ne hsub hne)
    have := ih (by omega)
    omega

theorem exists_fixed_point [Fintype V] :
    ∃ n ≤ Fintype.card V, frontier M n = frontier M (n + 1) := by
  by_contra hcon
  push_neg at hcon
  have hstrict : ∀ n ≤ Fintype.card V, frontier M n ≠ frontier M (n + 1) := hcon
  have hcard := card_frontier_ge_of_strict M hstrict (Fintype.card V + 1) le_rfl
  have hle : (frontier M (Fintype.card V + 1)).card ≤ Fintype.card V :=
    Finset.card_le_univ _ |>.trans (le_of_eq (Finset.card_univ))
  omega

theorem frontier_subset_closure [Fintype V] (n : ℕ) : frontier M n ⊆ closure M := by
  obtain ⟨k, hkN, hk⟩ := exists_fixed_point M
  rcases Nat.lt_or_ge n (Fintype.card V + 1) with hlt | hge
  · exact frontier_mono M (by omega)
  · have h1 : frontier M n = frontier M k :=
      frontier_stable_of_eq M hk n (le_trans hkN (by omega))
    have h2 : frontier M (Fintype.card V + 1) = frontier M k :=
      frontier_stable_of_eq M hk _ (by omega)
    rw [closure, h1, h2]

/-! ### The engine's closure is exactly the reachable set -/

theorem mem_closure_iff_reachable [Fintype V] {v : V} : v ∈ closure M ↔ Reachable M v := by
  constructor
  · intro hv; exact reachable_of_mem_frontier M hv
  · intro hv
    obtain ⟨n, hn⟩ := exists_mem_frontier_of_reachable M hv
    exact frontier_subset_closure M n hn

/-! ### Main theorem: soundness and completeness of the isolation engine -/

/-- **Soundness and completeness of the isolation engine.**

The engine reports an escape exactly when some object that the isolate does not own
is genuinely reachable from the isolate's roots by following references. -/
theorem null_escape_iff_unowned_reachable [Fintype V] :
    escapes M = true ↔ ∃ v, Reachable M v ∧ v ∉ M.owned := by
  rw [escapes, decide_eq_true_iff]
  constructor
  · rintro ⟨v, hv⟩
    rw [escapeSet, Finset.mem_sdiff] at hv
    exact ⟨v, (mem_closure_iff_reachable M).mp hv.1, hv.2⟩
  · rintro ⟨v, hv, hown⟩
    exact ⟨v, Finset.mem_sdiff.mpr ⟨(mem_closure_iff_reachable M).mpr hv, hown⟩⟩

/-- Contrapositive form: the isolate is leak-free (the engine reports no escape) iff
every object reachable from its roots is owned by it. -/
theorem no_escape_iff_all_reachable_owned [Fintype V] :
    escapes M = false ↔ ∀ v, Reachable M v → v ∈ M.owned := by
  have h := null_escape_iff_unowned_reachable M
  constructor
  · intro hfalse v hv
    by_contra hown
    rw [h.mpr ⟨v, hv, hown⟩] at hfalse
    exact Bool.noConfusion hfalse
  · intro hall
    by_contra hne
    obtain ⟨v, hv, hown⟩ := h.mp (by simpa using hne)
    exact hown (hall v hv)

/-! ### Worked examples

The engine is executable: on concrete finite models the verdict is decided by
kernel computation, and the main theorem transports it to the reachability
specification. -/

section Examples

/-- Object `0` is a root, it references `1`, which references `2`; the isolate owns
`0` and `1` but not `2`, so a reference escapes. -/
def leaky : Model (Fin 4) where
  succ := ![{1}, {2}, ∅, ∅]
  roots := {0}
  owned := {0, 1}

/-- The same graph, but object `3` (unowned) is unreachable from the roots, while
everything reachable is owned. -/
def sealed : Model (Fin 4) where
  succ := ![{1}, {0}, {3}, ∅]
  roots := {0}
  owned := {0, 1}

example : escapes leaky = true := by decide

example : ∃ v, Reachable leaky v ∧ v ∉ leaky.owned :=
  (null_escape_iff_unowned_reachable leaky).mp (by decide)

example : escapes sealed = false := by decide

example : ∀ v, Reachable sealed v → v ∈ sealed.owned :=
  (no_escape_iff_all_reachable_owned sealed).mp (by decide)

end Examples

end PCA.Isolation

import Mathlib
import RequestProject.Isolation

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

