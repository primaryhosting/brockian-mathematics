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

theorem inScope_root (p : List α) : InScope ⟨[[]], []⟩ p := by
  refine ⟨⟨[], by simp, by simp⟩, by simp⟩

/-! ## Worked example

A tenant scope that grants everything under `tenant1` except the `secret` subtree.
The facts below are checked by the kernel through `instDecidableInScope`, i.e. through
the verified encoding itself. -/

section Example

/-- Tenant 1 may see its own resources, except its `secret` subtree. -/
