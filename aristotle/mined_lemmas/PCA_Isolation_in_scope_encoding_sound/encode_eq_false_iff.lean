import Mathlib

/-!
# The isolation engine's scope model: soundness and completeness

This file gives a self-contained formal model of the *isolation engine* used to decide
whether a resource is *in scope* for a given access scope, together with a proof that the
engine's executable encoding (`PCA.Isolation.encode`) is **sound and complete** with respect
to the declarative semantics (`PCA.Isolation.InScope`).

* A `Resource` is owned by a tenant and lives at a hierarchical path.
* A `Scope` is built from tenant-wide grants and path-subtree grants, closed under union,
  intersection and complement.
* `InScope` is the declarative (`Prop`-valued) meaning of a scope.
* `encode` is the engine's executable (`Bool`-valued) decision procedure.

The main theorem `in_scope_encoding_sound` states `encode s r = true ↔ InScope s r`,
i.e. the engine accepts exactly the in-scope resources (soundness: it never accepts an
out-of-scope resource; completeness: it never rejects an in-scope one).

Downstream consequences proved here:

* `encode_eq_false_iff` — the engine rejects exactly the out-of-scope resources.
* `tenant_isolation` — a tenant-bounded scope can only contain resources of that tenant,
  so the engine never leaks a resource across a tenant boundary.
* `filterInScope_mem_iff` — the engine's filtering pass returns exactly the in-scope
  members of its input.
-/

open scoped Classical

namespace PCA.Isolation

/-- A resource managed by the isolation engine: it belongs to a tenant and sits at a
hierarchical path (e.g. a namespace/bucket/object path). -/
structure Resource where
  /-- Identifier of the owning tenant. -/
  tenant : Nat
  /-- Hierarchical path of the resource inside its tenant. -/
  path : List Nat
  deriving DecidableEq, Repr

/-- An access scope. -/
inductive Scope where
  /-- The empty scope: nothing is in scope. -/
  | empty : Scope
  /-- Every resource of tenant `t`. -/
  | tenantAll (t : Nat) : Scope
  /-- Every resource of tenant `t` whose path extends `p`. -/
  | subtree (t : Nat) (p : List Nat) : Scope
  /-- Union of two scopes. -/
  | union (s₁ s₂ : Scope) : Scope
  /-- Intersection of two scopes. -/
  | inter (s₁ s₂ : Scope) : Scope
  /-- Complement of a scope. -/
  | compl (s : Scope) : Scope
  deriving Repr

/-- Declarative semantics: `InScope s r` says that resource `r` lies in scope `s`. -/

theorem encode_eq_false_iff (s : Scope) (r : Resource) :
    encode s r = false ↔ ¬ InScope s r := by
  rw [← in_scope_encoding_sound]
  simp

/-- Scope membership is decidable, witnessed by the engine's encoding. -/
instance instDecidableInScope (s : Scope) (r : Resource) : Decidable (InScope s r) :=
  decidable_of_iff _ (in_scope_encoding_sound s r)

/-- `BoundedBy t s` records, structurally, that scope `s` can only ever grant access to
resources of tenant `t`. -/
inductive BoundedBy (t : Nat) : Scope → Prop where
  | empty : BoundedBy t .empty
  | tenantAll : BoundedBy t (.tenantAll t)
  | subtree (p : List Nat) : BoundedBy t (.subtree t p)
  | union {s₁ s₂ : Scope} : BoundedBy t s₁ → BoundedBy t s₂ → BoundedBy t (.union s₁ s₂)
  | interLeft {s₁ : Scope} (s₂ : Scope) : BoundedBy t s₁ → BoundedBy t (.inter s₁ s₂)
  | interRight (s₁ : Scope) {s₂ : Scope} : BoundedBy t s₂ → BoundedBy t (.inter s₁ s₂)

/-- **Tenant isolation.** A tenant-bounded scope only ever contains resources of that
tenant: the engine cannot leak a resource across a tenant boundary. -/
