import Mathlib

/-!
# A formal model of the isolation engine

This file develops a small, self-contained formal model of the *isolation engine*
used to split a constraint into independent, disjunction-free branches, and proves
its semantic correctness (soundness and completeness).

* `PCA.Isolation.Formula` — the constraint language: atoms, `⊤`, `⊥`, negation,
  conjunction and disjunction.
* `PCA.Isolation.eval` — its semantics, relative to an interpretation of atoms
  `I : A → E → Prop` over environments `E`.
* `PCA.Isolation.nnf` — the negation-normalisation phase.
* `PCA.Isolation.split` — the disjunction-splitting phase, producing a list of
  branches whose disjunction is equivalent to the input.
* `PCA.Isolation.isolate` — the whole engine: normalise, then split.

The main results are
`PCA.Isolation.disjunction_split_preserves_semantics` (an environment satisfies a
constraint iff it satisfies one of the isolated branches), together with the
soundness/completeness corollaries and the structural guarantee that every branch
produced by the engine is disjunction free.
-/

namespace PCA
namespace Isolation

universe u v

/-- Constraint formulas over an atom type `A`. -/
inductive Formula (A : Type u) where
  | tru : Formula A
  | fls : Formula A
  | atom : A → Formula A
  | neg : Formula A → Formula A
  | and : Formula A → Formula A → Formula A
  | or : Formula A → Formula A → Formula A
  deriving DecidableEq

variable {A : Type u} {E : Type v}

/-- Semantics of a constraint formula, relative to an interpretation `I` of the atoms
over environments of type `E`. -/

def nnf : Formula A → Bool → Formula A
  | Formula.tru, false => Formula.tru
  | Formula.tru, true => Formula.fls
  | Formula.fls, false => Formula.fls
  | Formula.fls, true => Formula.tru
  | Formula.atom a, false => Formula.atom a
  | Formula.atom a, true => Formula.neg (Formula.atom a)
  | Formula.neg f, p => nnf f (!p)
  | Formula.and f g, false => Formula.and (nnf f false) (nnf g false)
  | Formula.and f g, true => Formula.or (nnf f true) (nnf g true)
  | Formula.or f g, false => Formula.or (nnf f false) (nnf g false)
  | Formula.or f g, true => Formula.and (nnf f true) (nnf g true)

/-- A formula is in negation normal form when negation only occurs directly in
front of an atom. -/
