import Mathlib

/-!
# A formal model of a pointer-capability isolation engine

This file develops a small but complete formal model of the *isolation engine* used by a
pointer-capability analysis (`PCA`).

The model consists of

* a finite object graph `Graph V`, given by a successor (reference) function `succ`,
  an ownership predicate `owned` (`false` means the object is *unowned*, i.e. outside the
  isolation domain) and a finite set of `roots` (the entry points of the domain);
* an *inductive* specification of which objects are reachable from the roots (`Reachable`);
* an *executable* fixpoint engine (`closure`, `reachSet`, `escapeSet`) that computes the
  reachable set by saturation and reports the set of escaping objects.

The main results are

* `PCA.Isolation.mem_reachSet_iff` : the engine's reachable set is exactly the inductively
  specified reachable set (soundness and completeness of the reachability engine);
* `PCA.Isolation.mem_escapeSet_iff` : an object is reported as escaping iff it is reachable
  and unowned;
* `PCA.Isolation.null_escape_iff_unowned_reachable` : the engine reports no escape iff no
  unowned object is reachable from the roots.
-/

namespace PCA.Isolation

/-- A finite object graph together with an ownership predicate and a set of roots. -/
structure Graph (V : Type*) where
  /-- The objects directly referenced by an object. -/
  succ : V → Finset V
  /-- `owned v = true` means `v` belongs to the isolation domain. -/
  owned : V → Bool
  /-- Entry points of the isolation domain. -/
  roots : Finset V

variable {V : Type*} [DecidableEq V]

/-- Specification: the objects reachable from the roots by following references. -/
inductive Reachable (g : Graph V) : V → Prop
  | root {v : V} (hv : v ∈ g.roots) : Reachable g v
  | step {u v : V} (hu : Reachable g u) (huv : v ∈ g.succ u) : Reachable g v

/-- One saturation step of the engine: add all successors of the current set. -/
def expand (g : Graph V) (s : Finset V) : Finset V := s ∪ s.biUnion g.succ

lemma subset_expand (g : Graph V) (s : Finset V) : s ⊆ expand g s :=
  Finset.subset_union_left

lemma mem_expand_of_succ {g : Graph V} {s : Finset V} {u v : V} (hu : u ∈ s)
    (huv : v ∈ g.succ u) : v ∈ expand g s :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, hu, huv⟩)

lemma expand_subset {g : Graph V} {s t : Finset V} (hst : s ⊆ t)
    (ht : ∀ u ∈ t, ∀ v ∈ g.succ u, v ∈ t) : expand g s ⊆ t := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact hst hv
  · rcases Finset.mem_biUnion.mp hv with ⟨u, hu, huv⟩
    exact ht u (hst hu) v huv

/-- The engine: iterate `expand` until a fixpoint is reached. -/
def closure [Fintype V] (g : Graph V) (s : Finset V) : Finset V :=
  if expand g s ⊆ s then s else closure g (expand g s)
termination_by Fintype.card V - s.card
decreasing_by
  rename_i h
  have hss : s ⊂ expand g s := ⟨subset_expand g s, h⟩
  have hcard : s.card < (expand g s).card := Finset.card_lt_card hss
  have hle : (expand g s).card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ (expand g s)
  omega

lemma subset_closure [Fintype V] (g : Graph V) (s : Finset V) : s ⊆ closure g s := by
  fun_induction closure g s with
  | case1 s h => exact Finset.Subset.refl s
  | case2 s h ih => exact (subset_expand g s).trans ih

lemma closure_closed [Fintype V] (g : Graph V) (s : Finset V) :
    ∀ u ∈ closure g s, ∀ v ∈ g.succ u, v ∈ closure g s := by
  fun_induction closure g s with
  | case1 s h => exact fun u hu v huv => h (mem_expand_of_succ hu huv)
  | case2 s h ih => exact ih

lemma closure_least [Fintype V] {g : Graph V} {s t : Finset V} (hst : s ⊆ t)
    (ht : ∀ u ∈ t, ∀ v ∈ g.succ u, v ∈ t) : closure g s ⊆ t := by
  fun_induction closure g s with
  | case1 s h => exact hst
  | case2 s h ih => exact ih (expand_subset hst ht)

/-- The set of objects the engine considers reachable from the roots. -/
def reachSet [Fintype V] (g : Graph V) : Finset V := closure g g.roots

/-- Soundness and completeness of the reachability engine. -/
theorem mem_reachSet_iff [Fintype V] (g : Graph V) (v : V) : v ∈ reachSet g ↔ Reachable g v := by
  classical
  constructor
  · intro hv
    have hsub : reachSet g ⊆ Finset.univ.filter (fun w => Reachable g w) := by
      refine closure_least (fun w hw => ?_) (fun u hu w hw => ?_)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, Reachable.root hw⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ w, Reachable.step (Finset.mem_filter.mp hu).2 hw⟩
    exact (Finset.mem_filter.mp (hsub hv)).2
  · intro hv
    induction hv with
    | root hw => exact subset_closure g g.roots hw
    | step _ huv ih => exact closure_closed g g.roots _ ih _ huv

/-- The set of *escaping* objects: reachable from the roots but not owned by the domain. -/
def escapeSet [Fintype V] (g : Graph V) : Finset V := (reachSet g).filter (fun v => g.owned v = false)

/-- Soundness and completeness of the escape analysis. -/
theorem mem_escapeSet_iff [Fintype V] (g : Graph V) (v : V) :
    v ∈ escapeSet g ↔ Reachable g v ∧ g.owned v = false := by
  rw [escapeSet, Finset.mem_filter, mem_reachSet_iff]

/-- **Main theorem.** The isolation engine reports no escape exactly when no unowned object
is reachable from the roots of the domain. -/
theorem null_escape_iff_unowned_reachable [Fintype V] (g : Graph V) :
    escapeSet g = ∅ ↔ ¬ ∃ v : V, Reachable g v ∧ g.owned v = false := by
  constructor
  · intro h ⟨v, hv⟩
    have : v ∈ escapeSet g := (mem_escapeSet_iff g v).mpr hv
    rw [h] at this
    exact absurd this (Finset.notMem_empty v)
  · intro h
    refine Finset.eq_empty_of_forall_notMem (fun v hv => h ⟨v, ?_⟩)
    exact (mem_escapeSet_iff g v).mp hv

/-- Contrapositive form: a nonempty escape set witnesses an unowned reachable object. -/
theorem escape_nonempty_iff_unowned_reachable [Fintype V] (g : Graph V) :
    (escapeSet g).Nonempty ↔ ∃ v : V, Reachable g v ∧ g.owned v = false := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, null_escape_iff_unowned_reachable, not_not]


/-! ### Worked examples

Two small instances showing that both sides of the main theorem are inhabited, i.e. that the
statement is not vacuous.
-/

namespace Example

/-- A leaking configuration: object `0` (a root, owned) references `1` (owned), which
references `2`, which is *not* owned by the domain. -/
def leaky : Graph (Fin 3) where
  succ := ![{1}, {2}, ∅]
  owned := ![true, true, false]
  roots := {0}

lemma reachable_leaky_two : Reachable leaky 2 :=
  Reachable.step (v := 2) (Reachable.step (u := 0) (v := 1) (Reachable.root (by decide))
    (by decide)) (by decide)

/-- The engine detects the escape of object `2`. -/
lemma leaky_escapes : (escapeSet leaky).Nonempty :=
  (escape_nonempty_iff_unowned_reachable leaky).mpr ⟨2, reachable_leaky_two, by decide⟩

/-- An isolated configuration: the domain `{0, 1}` is closed under references, and the
unowned object `2` is not reachable from the root `0`. -/
def isolated : Graph (Fin 3) where
  succ := ![{1}, {0}, ∅]
  owned := ![true, true, false]
  roots := {0}

lemma reachable_isolated (v : Fin 3) (hv : Reachable isolated v) : v = 0 ∨ v = 1 := by
  induction hv with
  | root hw => left; simpa [isolated] using hw
  | step _ huv ih => rcases ih with rfl | rfl <;> simp [isolated] at huv <;> simp [huv]

/-- The engine reports no escape for the isolated configuration. -/
lemma isolated_no_escape : escapeSet isolated = ∅ := by
  refine (null_escape_iff_unowned_reachable isolated).mpr ?_
  rintro ⟨v, hv, hunowned⟩
  rcases reachable_isolated v hv with rfl | rfl <;> simp [isolated] at hunowned

end Example

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

