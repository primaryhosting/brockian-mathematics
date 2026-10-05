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
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Invariant

universe u

/-- The two possible outcomes of a policy evaluation performed by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

/-- An access request: a principal performing an action on a resource. -/
structure Request (P A R : Type u) where
  principal : P
  action : A
  resource : R

/-- A matching pattern used inside an allow-rule: either a wildcard, or an exact value. -/
inductive Pattern (α : Type u)
  | any
  | exact (a : α)

namespace Pattern

variable {α : Type u}

/-- Declarative (propositional) semantics of pattern matching. -/

def matchesB [DecidableEq P] [DecidableEq A] [DecidableEq R]
    (rule : Rule P A R) (req : Request P A R) : Bool :=
  rule.principal.matchesB req.principal &&
  rule.action.matchesB req.action &&
  rule.resource.matchesB req.resource

/-- The executable rule matcher agrees with the declarative semantics. -/
@[simp]
