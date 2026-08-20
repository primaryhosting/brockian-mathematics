import Mathlib

/-!
# A formal model of an isolation engine's scope decision procedure

This file gives a self-contained formal model of the *isolation engine* used to decide
whether a resource is "in scope" for a given isolation scope, together with the
soundness **and** completeness statement for the boolean *encoding* the engine actually
evaluates.

## The model

* Resources are identified by hierarchical **labels** (`PCA.Isolation.Label`), i.e. paths
  in a naming tree, represented as lists of path components.
* An isolation **scope** (`PCA.Isolation.Scope`) is given by a list of *allow roots* and a
  list of *deny roots*.
* The **semantics** (`PCA.Isolation.InScope`) says: a label is in scope iff some allow root
  is a prefix of it and no deny root is a prefix of it.
* The engine does not evaluate this semantics directly.  It *compiles* a scope into a
  propositional formula (`PCA.Isolation.Formula`) over prefix-test atoms
  (`PCA.Isolation.encodeScope`), and evaluates that formula against the atom valuation
  induced by the resource label (`PCA.Isolation.prefixEnv`).

The main theorem `PCA.Isolation.in_scope_encoding_sound` states that this compilation is
both sound and complete: the compiled formula evaluates to `true` exactly on the labels
that are semantically in scope.
-/

namespace PCA.Isolation

/-- A hierarchical resource label: a path in the naming tree. -/
abbrev Label := List String

/-- An isolation scope: a list of allow roots together with a list of deny roots. -/
structure Scope where
  /-- Roots granting access to their whole subtree. -/
  allow : List Label
  /-- Roots revoking access to their whole subtree, overriding `allow`. -/
  deny : List Label
  deriving Repr, DecidableEq

/-- Semantics of a scope: `x` is in scope when it lies under some allow root and under no
deny root. -/

def InScope (s : Scope) (x : Label) : Prop :=
  (∃ r ∈ s.allow, r <+: x) ∧ ∀ e ∈ s.deny, ¬ (e <+: x)

/-- Propositional formulas over atoms of type `α`; the intermediate representation the
isolation engine evaluates. -/
inductive Formula (α : Type) where
  | tt : Formula α
  | ff : Formula α
  | atom : α → Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  deriving Repr

/-- Evaluation of a formula under a valuation of atoms. -/
