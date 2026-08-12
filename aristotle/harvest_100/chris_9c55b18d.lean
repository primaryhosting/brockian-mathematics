/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace PCA
namespace Isolation

universe u

/-- Syntax of isolation constraints over a type `α` of atomic predicates
(e.g. "capability `c` is granted", "resource `r` is reachable"). -/
inductive Constraint (α : Type u) : Type u
  | atom : α → Constraint α
  | tru : Constraint α
  | fls : Constraint α
  | neg : Constraint α → Constraint α
  | conj : Constraint α → Constraint α → Constraint α
  | disj : Constraint α → Constraint α → Constraint α
  deriving Repr

namespace Constraint

variable {α : Type u}

/-- Semantics of an isolation constraint relative to a valuation `v` of the atoms. -/
def eval (v : α → Prop) : Constraint α → Prop
  | atom a => v a
  | tru => True
  | fls => False
  | neg c => ¬ eval v c
  | conj c d => eval v c ∧ eval v d
  | disj c d => eval v c ∨ eval v d

/-- The isolation engine's *disjunction split*: a constraint is decomposed into the
list of its top-level disjuncts, so that each branch can be discharged separately. -/
def split : Constraint α → List (Constraint α)
  | disj c d => split c ++ split d
  | c => [c]

/-- A constraint has no top-level disjunction. -/
def disjFree : Constraint α → Prop
  | disj _ _ => False
  | _ => True

@[simp] theorem split_disj (c d : Constraint α) :
    split (disj c d) = split c ++ split d := rfl

theorem split_ne_nil (c : Constraint α) : split c ≠ [] := by
  induction c with
  | disj c d ihc _ =>
      intro h
      rw [split_disj] at h
      exact ihc (List.append_eq_nil_iff.mp h).1
  | _ => simp [split]

/-- Every branch produced by the split is free of top-level disjunctions:
the split is exhaustive. -/
theorem disjFree_of_mem_split {c b : Constraint α} (hb : b ∈ split c) : disjFree b := by
  induction c with
  | disj c d ihc ihd =>
      rcases List.mem_append.mp hb with h | h
      · exact ihc h
      · exact ihd h
  | atom a => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | tru => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | fls => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | neg c _ => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | conj c d _ _ => simp only [split, List.mem_singleton] at hb; subst hb; trivial

end Constraint

open Constraint

/-- **Disjunction split preserves semantics.**  For every valuation `v` and every
isolation constraint `c`, the constraint holds exactly when one of the branches
produced by `split` holds.  The forward direction is completeness of the split
(no model is lost) and the backward direction is its soundness (no model is added). -/
theorem disjunction_split_preserves_semantics {α : Type u} (v : α → Prop)
    (c : Constraint α) :
    eval v c ↔ ∃ b ∈ split c, eval v b := by
  induction c with
  | disj c d ihc ihd =>
      -- `List.mem_append` is the key rewriting lemma here.
      simp only [split_disj, List.mem_append, eval]
      constructor
      · rintro (h | h)
        · obtain ⟨b, hb, hbe⟩ := ihc.mp h
          exact ⟨b, Or.inl hb, hbe⟩
        · obtain ⟨b, hb, hbe⟩ := ihd.mp h
          exact ⟨b, Or.inr hb, hbe⟩
      · rintro ⟨b, hb | hb, hbe⟩
        · exact Or.inl (ihc.mpr ⟨b, hb, hbe⟩)
        · exact Or.inr (ihd.mpr ⟨b, hb, hbe⟩)
  | atom a => simp [split]
  | tru => simp [split]
  | fls => simp [split, eval]
  | neg c _ => simp [split]
  | conj c d _ _ => simp [split]

/-- Soundness of the split: any satisfied branch witnesses the original constraint. -/
theorem disjunction_split_sound {α : Type u} (v : α → Prop) (c b : Constraint α)
    (hb : b ∈ split c) (h : eval v b) : eval v c :=
  (disjunction_split_preserves_semantics v c).mpr ⟨b, hb, h⟩

/-- Completeness of the split: every model of the constraint satisfies some branch. -/
theorem disjunction_split_complete {α : Type u} (v : α → Prop) (c : Constraint α)
    (h : eval v c) : ∃ b ∈ split c, eval v b :=
  (disjunction_split_preserves_semantics v c).mp h

end Isolation
end PCA

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

