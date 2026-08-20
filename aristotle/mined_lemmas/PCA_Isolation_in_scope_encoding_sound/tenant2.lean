import Mathlib

/-!
# A formal model of the isolation engine's scope check

This file gives a self-contained formal model of the *isolation engine* used to decide
whether a resource (identified by a hierarchical path) is inside a given isolation
scope, together with a proof that the executable (boolean) encoding of the check is
**sound and complete** with respect to the declarative specification.

## The model

* A resource path is a `List α` of path segments (e.g. `["tenant", "db", "table"]`).
* An isolation `Scope` consists of a list of *allow* prefixes and a list of *deny*
  prefixes.
* Declaratively (`InScope`), a path is in scope when some allow prefix is a prefix of
  the path and no deny prefix is a prefix of the path — i.e. deny always overrides
  allow.
* Operationally (`encodeInScope`), the engine evaluates a boolean expression built from
  `List.isPrefixOf` tests.

The main theorem `PCA.Isolation.in_scope_encoding_sound` states that the boolean
encoding returns `true` exactly on the paths that satisfy the declarative
specification; soundness and completeness are the two directions of this equivalence.
-/

namespace PCA.Isolation

universe u

variable {α : Type u}

/-- An isolation scope: a list of allowed path prefixes and a list of denied path
prefixes. -/
structure Scope (α : Type u) where
  /-- Path prefixes that grant access. -/
  allows : List (List α)
  /-- Path prefixes that revoke access; deny overrides allow. -/
  denies : List (List α)
  deriving Repr

/-- Declarative specification of the isolation check: the path `p` is in the scope `s`
when some allow prefix matches `p` and no deny prefix matches `p`. -/

def tenant2 : Scope String :=
  ⟨[["tenant2"]], [["tenant1"]]⟩

example : InScope tenant1 ["tenant1", "db", "users"] := by decide

example : ¬ InScope tenant1 ["tenant1", "secret", "key"] := by decide

example : ¬ InScope tenant1 ["tenant2", "db"] := by decide

example : ¬ InScope tenant1 ["tenant10", "db"] := by decide

example :
    filterInScope tenant1 [["tenant1", "db"], ["tenant1", "secret", "key"], ["tenant2"]]
      = [["tenant1", "db"]] := by decide

/-- The two tenant scopes are isolated from each other: no resource is visible to both. -/
example (p : List String) : InScope tenant1 p → ¬ InScope tenant2 p := by
  refine inScope_disjoint ?_ p
  intro a ha
  simp only [tenant1, List.mem_singleton] at ha
  subst ha
  exact ⟨["tenant1"], by simp [tenant2], List.prefix_refl _⟩

end Example

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

