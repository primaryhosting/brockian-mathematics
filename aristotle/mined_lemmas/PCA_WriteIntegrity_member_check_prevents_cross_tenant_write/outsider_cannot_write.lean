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

theorem outsider_cannot_write
    (P : Policy) (s : Store) (trace : List WriteReq) (a : Principal) (i : ResourceId)
    (hactor : ∀ r ∈ trace, r.actor = a)
    (hout : ¬ P.member a (P.owner i)) :
    run P s trace i = s i :=
  member_check_prevents_cross_tenant_write P s trace i
    (fun r hr => by rw [hactor r hr]; exact hout)

/-- Attribution: if the store changed at `i` over a trace, then some request in
the trace targeted `i`, passed the member check, and its actor really is a
member of the tenant owning `i`. -/
