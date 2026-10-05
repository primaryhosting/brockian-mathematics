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

theorem member_write_succeeds
    (P : Policy) (s : Store) (r : WriteReq)
    (h : P.member r.actor (P.owner r.target)) :
    step P s r r.target = r.value :=
  step_target_of_authorized P s r h

/-! ## A concrete instance

A two-tenant example checked by `decide`, confirming the model is not vacuous:
principal `0` belongs to tenant `0`, principal `1` to tenant `1`; resource `0`
is owned by tenant `0` and resource `1` by tenant `1`. -/

/-- Example policy: principal `p` is a member of tenant `t` iff `p = t`. -/
