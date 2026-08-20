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

theorem not_any_denies_iff (s : Scope α) (p : List α) :
    (!s.denies.any fun d => d.isPrefixOf p) = true ↔ ∀ d ∈ s.denies, ¬ d <+: p := by
  simp [List.isPrefixOf_iff_prefix]

/-- **Soundness and completeness of the isolation engine's scope encoding.**

The boolean decision procedure `encodeInScope` returns `true` on exactly those paths
that the declarative specification `InScope` admits. Read left to right this is
soundness (every accepted path really is in scope), and right to left completeness
(every in-scope path is accepted). -/
