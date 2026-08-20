import Mathlib

/-!
# A formal model of the isolation engine's constraint language

This file develops a small, self-contained model of the constraint language used by an
*isolation engine*: policies are propositional constraints over abstract atoms, and the
engine works by *splitting disjunctions*, i.e. by rewriting a policy into a finite list of
disjunction-free branches (cubes) whose disjunction is semantically equivalent to the
original policy.

The main result is `PCA.Isolation.disjunction_split_preserves_semantics`, which states
that the disjunction split is both **sound** (every model of a branch is a model of the
policy) and **complete** (every model of the policy is a model of some branch).

Supporting results:

* `PCA.Isolation.split_isCube` — every branch produced by the split is a cube, i.e. a
  conjunction of literals, containing no disjunction (negations are pushed to the atoms).
* `PCA.Isolation.isolated_iff_branches` — an isolation query reduces exactly to the
  finitely many cube-vs-cube queries on the branches.
* `PCA.Isolation.sat_iff_branch_sat` — a policy is satisfiable iff some branch is.
-/

namespace PCA.Isolation

universe u

variable {α : Type u}

/-- Policies of the isolation engine: propositional constraints over abstract atoms. -/
inductive Formula (α : Type u) where
  | atom : α → Formula α
  | tru : Formula α
  | fls : Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  deriving Repr, DecidableEq

/-- Semantics of a policy relative to a valuation `v` of the atoms. -/

theorem sat_iff_branch_sat (f : Formula α) :
    (∃ v : α → Prop, eval v f) ↔ ∃ b ∈ split f, ∃ v : α → Prop, eval v b := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨b, hb, hbv⟩ := disjunction_split_complete v f hv
    exact ⟨b, hb, v, hbv⟩
  · rintro ⟨b, hb, v, hbv⟩
    exact ⟨v, disjunction_split_sound v f b hb hbv⟩

section Examples

/-- De Morgan is carried out by the split: the negation of a disjunction of two atoms
splits into the single cube consisting of the two negated atoms. -/
example (a b : ℕ) :
    split (Formula.neg (Formula.disj (Formula.atom a) (Formula.atom b))) =
      [Formula.conj (Formula.neg (Formula.atom a)) (Formula.neg (Formula.atom b))] := rfl

/-- A disjunction of two atoms splits into two branches. -/
example (a b : ℕ) :
    split (Formula.disj (Formula.atom a) (Formula.atom b)) =
      [Formula.atom a, Formula.atom b] := rfl

/-- An atom and its negation are isolated. -/
example (a : ℕ) : Isolated (Formula.atom a) (Formula.neg (Formula.atom a)) := by
  rintro v ⟨h1, h2⟩
  exact h2 h1

end Examples

end PCA.Isolation

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

