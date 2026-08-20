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
# A formal model of a multi-tenant write-isolation engine

This file develops a small but complete operational model of the write path of a
multi-tenant isolation engine ("PCA"), together with soundness and completeness
theorems for its membership check.

* `PCA.WriteIntegrity.Config` is the (static) isolation configuration: which tenant owns
  each resource, and which principals are members of which tenant.
* `PCA.WriteIntegrity.authorize` is the executable membership check performed by the engine
  on each write request.
* `PCA.WriteIntegrity.step` / `PCA.WriteIntegrity.run` are the operational semantics: a write
  request mutates the store exactly when the check succeeds, and is a no-op otherwise.

The main results are

* `PCA.WriteIntegrity.authorize_iff` : the executable check is *sound and complete*
  with respect to the declarative membership specification;
* `PCA.WriteIntegrity.member_check_prevents_cross_tenant_write` : along any trace of
  requests, if the contents of a resource change then some request in the trace targeted
  that resource and was issued by a principal that is a member of the tenant owning it —
  i.e. no cross-tenant write can ever take effect;
* `PCA.WriteIntegrity.run_eq_of_no_member_request` : the contrapositive form (traces made
  entirely of cross-tenant requests are observationally inert);
* `PCA.WriteIntegrity.authorized_write_effective` : the engine does not over-block, an
  in-tenant write does take effect.
-/

namespace PCA
namespace WriteIntegrity

/-- Tenant identifiers. -/
abbrev Tenant := Nat
/-- Principal (user / service account) identifiers. -/
abbrev Principal := Nat
/-- Resource (object) identifiers. -/
abbrev Resource := Nat
/-- Values stored in resources. -/
abbrev Value := Nat

/-- The static isolation configuration: every resource belongs to exactly one tenant,
and membership of principals in tenants is decided by an executable predicate. -/
structure Config where
  /-- The tenant owning a given resource. -/
  owner : Resource → Tenant
  /-- The engine's membership table. -/
  memberOf : Principal → Tenant → Bool

/-- Declarative reading of the membership table. -/

def CrossTenant (c : Config) (q : Request) : Prop :=
  ¬ c.Member q.principal (c.owner q.resource)

/-- The store: current contents of every resource. -/
abbrev Store := Resource → Value

/-- The engine's membership check on a write request. -/
