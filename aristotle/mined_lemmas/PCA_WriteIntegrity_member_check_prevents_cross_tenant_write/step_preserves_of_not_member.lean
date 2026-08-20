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

theorem step_preserves_of_not_member (E : Env) (s : State) (q : WriteReq)
    {t : TenantId} (hq : E.member q.actor t = false)
    {r : ResourceId} (hr : E.owner r = t) :
    (step E s q).store r = s.store r := by
  by_cases h : r = q.target
  · subst h
    have hg : guard E q = false := by
      unfold guard
      rw [hr]
      exact hq
    simp [step, hg]
  · exact step_store_of_ne E s q h

/-! ## Main theorem -/

/-- **Member check prevents cross-tenant writes.**  If no actor occurring in a
trace of write requests is a member of tenant `t`, then after running the whole
trace every resource owned by `t` still holds its initial value. -/
