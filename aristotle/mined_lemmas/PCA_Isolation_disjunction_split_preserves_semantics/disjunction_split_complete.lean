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

theorem disjunction_split_complete (v : α → Prop) (f : Formula α) (h : eval v f) :
    ∃ b ∈ split f, eval v b :=
  (disjunction_split_preserves_semantics v f).mp h

/-- Every branch produced by the polarised split is a cube, hence disjunction-free. -/
