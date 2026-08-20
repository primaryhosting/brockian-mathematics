/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA
namespace WriteIntegrity

/-! ## The isolation engine's model

We model a multi-tenant write path.  A static environment records which
principals are members of which tenants, and which tenant owns each resource.
The engine's only guard before performing a write is a *member check*: the
actor must be a member of the tenant that owns the targeted resource.

The main theorem says this single check is enough to guarantee tenant
isolation for writes: along an arbitrary trace of write requests, if no actor
appearing in the trace is a member of tenant `t`, then every resource owned by
`t` retains its original value. -/

/-- Tenant identifiers. -/
abbrev TenantId := Nat
/-- Principal (user) identifiers. -/
abbrev UserId := Nat
/-- Resource identifiers. -/
abbrev ResourceId := Nat
/-- Stored values. -/
abbrev Value := Nat

/-- Static environment: tenant membership of principals, tenant ownership of
resources. -/
structure Env where
  /-- `member u t` holds when principal `u` is a member of tenant `t`. -/
  member : UserId → TenantId → Bool
  /-- `owner r` is the tenant that owns resource `r`. -/
  owner : ResourceId → TenantId

/-- Mutable state of the store. -/
structure State where
  /-- Current value of each resource. -/
  store : ResourceId → Value

/-- A write request: a principal asks to set a resource to a value. -/
structure WriteReq where
  /-- The principal issuing the request. -/
  actor : UserId
  /-- The resource being written. -/
  target : ResourceId
  /-- The value to be written. -/
  val : Value

/-- Declarative access-control policy: a write of `r` by `u` is permitted
exactly when `u` is a member of the tenant owning `r`. -/

theorem step_store_of_ne (E : Env) (s : State) (q : WriteReq) {r : ResourceId}
    (h : r ≠ q.target) : (step E s q).store r = s.store r := by
  unfold step
  by_cases hg : guard E q <;> simp [hg, h]

/-! ## Key intermediate lemma -/

/-- **Key lemma.** A single step by a principal that is not a member of tenant
`t` cannot modify any resource owned by `t`. -/
