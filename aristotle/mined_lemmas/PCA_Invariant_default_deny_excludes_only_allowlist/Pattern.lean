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

/-!
# A formal model of a default-deny isolation engine

This file develops a small, self-contained model of a *policy controlled access* (PCA)
isolation engine and proves its central security invariant: the engine is **default deny**,
so the set of requests it admits is *exactly* the set of requests captured by the
allowlist (minus anything the denylist covers).  Nothing else can slip through.

The two halves of the statement are:

* **soundness**  – every admitted request is matched by some allowlist rule
  (and by no denylist rule);
* **completeness** – every request matched by an allowlist rule and by no denylist rule
  is admitted.

Together these say the engine's behaviour is characterised by its policy, which is
`PCA.Invariant.default_deny_excludes_only_allowlist`.
-/

namespace PCA

/-- A *pattern* for one field of a request: `Pattern.any` is a wildcard, while
`Pattern.exact s` matches the single label `s`. -/
inductive Pattern (α : Type) where
  | any : Pattern α
  | exact : α → Pattern α
  deriving DecidableEq, Repr

/-- Does a field pattern match a concrete label? -/

def Pattern.Matches {α : Type} (p : Pattern α) (a : α) : Prop :=
  match p with
  | .any => True
  | .exact b => b = a

instance {α : Type} [DecidableEq α] (p : Pattern α) (a : α) : Decidable (p.Matches a) := by
  cases p <;> simp [Pattern.Matches] <;> infer_instance

/-- A request presented to the isolation engine: a principal in some domain asks to
perform an action on a resource. -/
structure Request (Principal Resource Action : Type) where
  principal : Principal
  resource : Resource
  action : Action
  deriving DecidableEq, Repr

/-- A policy rule: a triple of patterns, one for each field of a request. -/
structure Rule (Principal Resource Action : Type) where
  principal : Pattern Principal
  resource : Pattern Resource
  action : Pattern Action
  deriving DecidableEq, Repr

variable {Principal Resource Action : Type}

/-- A rule matches a request when all three of its field patterns match. -/
