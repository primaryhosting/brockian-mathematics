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
def InScope : Scope → Resource → Prop
  | .empty, _ => False
  | .tenantAll t, r => r.tenant = t
  | .subtree t p, r => r.tenant = t ∧ p <+: r.path
  | .union s₁ s₂, r => InScope s₁ r ∨ InScope s₂ r
  | .inter s₁ s₂, r => InScope s₁ r ∧ InScope s₂ r
  | .compl s, r => ¬ InScope s r

/-- The isolation engine's executable encoding of scope membership. -/
def encode : Scope → Resource → Bool
  | .empty, _ => false
  | .tenantAll t, r => r.tenant == t
  | .subtree t p, r => (r.tenant == t) && p.isPrefixOf r.path
  | .union s₁ s₂, r => encode s₁ r || encode s₂ r
  | .inter s₁ s₂, r => encode s₁ r && encode s₂ r
  | .compl s, r => !encode s r

/-- **Soundness and completeness of the isolation engine's encoding.**
The engine accepts a resource exactly when it is in scope. -/
theorem in_scope_encoding_sound (s : Scope) (r : Resource) :
    encode s r = true ↔ InScope s r := by
  induction s with
  | empty => simp [encode, InScope]
  | tenantAll t => simp [encode, InScope]
  | subtree t p => simp [encode, InScope, List.isPrefixOf_iff_prefix]
  | union s₁ s₂ ih₁ ih₂ => simp [encode, InScope, ih₁, ih₂]
  | inter s₁ s₂ ih₁ ih₂ => simp [encode, InScope, ih₁, ih₂]
  | compl s ih => simp [encode, InScope, ← ih]

/-- The engine rejects exactly the out-of-scope resources. -/
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
theorem tenant_isolation {t : Nat} {s : Scope} (hs : BoundedBy t s) {r : Resource}
    (hr : InScope s r) : r.tenant = t := by
  induction hs with
  | empty => exact absurd hr (by simp [InScope])
  | tenantAll => exact hr
  | subtree p => exact hr.1
  | union _ _ ih₁ ih₂ => exact hr.elim ih₁ ih₂
  | interLeft _ _ ih => exact ih hr.1
  | interRight _ _ ih => exact ih hr.2

/-- The corresponding statement about the engine's encoding. -/
theorem tenant_isolation_encode {t : Nat} {s : Scope} (hs : BoundedBy t s) {r : Resource}
    (hr : encode s r = true) : r.tenant = t :=
  tenant_isolation hs ((in_scope_encoding_sound s r).mp hr)

/-- The engine's filtering pass: keep exactly the resources the encoding accepts. -/
def filterInScope (s : Scope) (rs : List Resource) : List Resource :=
  rs.filter (encode s)

/-- **Soundness and completeness of the filtering pass**: it returns exactly the in-scope
members of its input. -/
theorem filterInScope_mem_iff (s : Scope) (rs : List Resource) (r : Resource) :
    r ∈ filterInScope s rs ↔ r ∈ rs ∧ InScope s r := by
  simp [filterInScope, List.mem_filter, in_scope_encoding_sound]

/-- Subtree scopes are closed under extending the path: a deeper resource under a granted
prefix stays in scope. -/
theorem inScope_subtree_append (t : Nat) (p q : List Nat) :
    InScope (.subtree t p) ⟨t, p ++ q⟩ :=
  ⟨rfl, ⟨q, rfl⟩⟩

/-- Nothing is in the empty scope, and everything is in its complement. -/
theorem inScope_compl_empty (r : Resource) : InScope (.compl .empty) r := by
  simp [InScope]

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

