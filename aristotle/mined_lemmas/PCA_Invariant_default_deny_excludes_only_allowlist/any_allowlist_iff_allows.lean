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

This file develops a small but complete model of the access-control ("isolation")
engine of a *policy-controlled agent* (`PCA`), together with the formal
soundness and completeness statement of its central security invariant:

> **Default deny.**  The engine denies every capability request, *except* exactly
> those that are explicitly matched by a rule of the policy's allowlist.

The model consists of

* `PCA.Capability`   — a concrete capability request (subject, action, resource);
* `PCA.Pattern`      — a matcher for one field, either a wildcard or an exact value;
* `PCA.Rule`         — an allowlist entry, i.e. a triple of patterns;
* `PCA.Policy`       — an allowlist of rules (and nothing else: there is no deny list,
                        denial is the default);
* `PCA.evaluate`     — the decision procedure of the engine.

The main theorem is `PCA.Invariant.default_deny_excludes_only_allowlist`.
-/

namespace PCA

/-- The decision returned by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

/-- A concrete capability request: a subject asking to perform an action on a resource. -/
structure Capability where
  subject : String
  action : String
  resource : String
  deriving DecidableEq, Repr

/-- A matcher for a single field of a capability: either a wildcard, or an exact value. -/
inductive Pattern
  | any
  | exact (value : String)
  deriving DecidableEq, Repr

/-- When does a pattern match a concrete field value? -/

theorem any_allowlist_iff_allows (p : Policy) (c : Capability) :
    (p.allowlist.any fun rl => decide (rl.Matches c)) = true ↔ p.Allows c := by
  simp [Policy.Allows, List.any_eq_true]

/-- **Completeness.**  Every capability matched by the allowlist is allowed. -/
