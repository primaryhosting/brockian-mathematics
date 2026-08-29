/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.WriteIntegrity

/-- Tenant identifiers. -/
abbrev Tenant := Nat
/-- Principal (user / service account) identifiers. -/
abbrev Principal := Nat
/-- Resource identifiers. -/
abbrev ResourceId := Nat
/-- Values stored in resources. -/
abbrev Value := Nat

/-- The isolation policy of the engine: which principals are members of which
tenant, and which tenant owns which resource. -/
structure Policy where
  /-- `member p t` holds when principal `p` is a member of tenant `t`. -/
  member : Principal → Tenant → Bool
  /-- `owner i` is the tenant owning resource `i`. -/
  owner : ResourceId → Tenant

/-- A write request: an actor asking to set a resource to a value. -/
structure WriteReq where
  /-- The principal issuing the request. -/
  actor : Principal
  /-- The resource to be written. -/
  target : ResourceId
  /-- The value to be written. -/
  value : Value

/-- The state of the store: a value for every resource. -/
abbrev Store := ResourceId → Value

/-- Point update of the store. -/

theorem step_ne_imp (P : Policy) (s : Store) (r : WriteReq) (i : ResourceId)
    (h : step P s r i ≠ s i) : r.target = i ∧ authorized P r := by
  by_cases ha : authorized P r
  · refine ⟨?_, ha⟩
    by_cases hEq : i = r.target
    · exact hEq.symm
    · exact absurd (by simp [step, ha, Store.write_of_ne _ _ hEq]) h
  · exact absurd (by simp [step, ha]) h

/-- **Main theorem (cross-tenant write prevention).**
If every request in a trace is issued by a principal that is *not* a member of
the tenant owning resource `i`, then the engine's final store agrees with the
initial store at `i`: no cross-tenant write can occur. -/
