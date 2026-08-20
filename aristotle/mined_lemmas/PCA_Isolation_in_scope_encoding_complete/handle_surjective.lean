import Mathlib

/-!
# A formal model of a scope-isolation engine, with soundness and completeness

This file develops a small, fully formal model of the *isolation engine* used to hand out
opaque handles ("encodings") for resources that lie inside a caller's scope.

The model:

* A `Resource` is owned by a tenant and has a resource identifier.
* A `Scope` is a tenant together with the finite set of resource identifiers the caller
  is allowed to observe.
* `PCA.Isolation.InScope` is the ground-truth access predicate.
* `PCA.Isolation.encode` is the engine: it turns an in-scope resource into a dense index
  (a handle) and refuses (`none`) on anything out of scope.
* `PCA.Isolation.decode` is the inverse direction used to resolve a handle back to a resource.

The main results are:

* `PCA.Isolation.in_scope_encoding_complete` — soundness *and* completeness of the engine:
  a resource is in scope **iff** the engine issues a valid, in-range handle for it that
  decodes back to exactly that resource.
* `PCA.Isolation.encode_sound`, `PCA.Isolation.decode_sound` — no handle is ever produced
  for, or resolves to, an out-of-scope resource.
* `PCA.Isolation.cross_tenant_isolation` — resources of a foreign tenant are never encoded.
* `PCA.Isolation.encode_injective_on_scope` — distinct in-scope resources get distinct handles.
* `PCA.Isolation.handle_surjective` — every index below the scope size is a live handle.
-/

namespace PCA.Isolation

/-- Tenants are identified by a natural number. -/
abbrev Tenant := ℕ

/-- Resource identifiers are natural numbers. -/
abbrev ResId := ℕ

/-- A resource is owned by a tenant and carries a resource identifier. -/
structure Resource where
  tenant : Tenant
  rid : ResId
deriving DecidableEq, Repr

/-- A scope is the authority of one tenant over a finite set of resource identifiers. -/
structure Scope where
  tenant : Tenant
  allowed : Finset ResId

/-- The ground-truth access predicate: `r` is visible in scope `s` when it belongs to the
scope's tenant and its identifier is explicitly allowed. -/

theorem handle_surjective {s : Scope} {i : ℕ} (hi : i < s.allowed.card) :
    ∃ r, InScope s r ∧ encode s r = some i ∧ decode s i = some r := by
  have hlt : i < (handles s).length := by simpa [length_handles] using hi
  refine ⟨⟨s.tenant, (handles s)[i]⟩, ?_⟩
  have hdec : decode s i = some ⟨s.tenant, (handles s)[i]⟩ := by
    unfold decode
    rw [List.getElem?_eq_getElem hlt]
    simp
  obtain ⟨hs, henc, -⟩ := decode_sound hdec
  exact ⟨hs, henc, hdec⟩

/-! ### A concrete instance, showing the model is not vacuous -/

section Example

/-- Tenant `0` may see resources `3` and `7`. -/
