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

theorem change_implies_member (E : Env) (s : State) (tr : List WriteReq)
    {r : ResourceId} (h : (run E s tr).store r ≠ s.store r) :
    ∃ q ∈ tr, q.target = r ∧ MayWrite E q.actor r := by
  induction tr generalizing s with
  | nil => exact absurd rfl h
  | cons q qs ih =>
      rw [run] at h
      by_cases hstep : (step E s q).store r = s.store r
      · have h' : (run E (step E s q) qs).store r ≠ (step E s q).store r := by
          rw [hstep]; exact h
        obtain ⟨p, hp, hp1, hp2⟩ := ih (s := step E s q) h'
        exact ⟨p, List.mem_cons_of_mem _ hp, hp1, hp2⟩
      · have htgt : r = q.target := by
          by_cases hne : r = q.target
          · exact hne
          · exact absurd (step_store_of_ne E s q hne) hstep
        have hg : guard E q = true := by
          by_cases hg : guard E q
          · exact hg
          · exact absurd (by simp [step, hg]) hstep
        refine ⟨q, List.mem_cons_self .., htgt.symm, ?_⟩
        show E.member q.actor (E.owner r) = true
        rw [htgt]
        exact hg

/-- Contrapositive packaging of the main theorem: a cross-tenant actor can
never be the cause of a change to another tenant's resource. -/
