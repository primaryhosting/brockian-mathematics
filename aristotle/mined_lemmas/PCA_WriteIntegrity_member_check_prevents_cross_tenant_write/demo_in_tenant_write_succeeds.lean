/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA
namespace WriteIntegrity

/-! ## The isolation engine model

A minimal multi-tenant key–value service.  Every principal belongs to a tenant and
every resource is owned by a tenant.  A write request is executed only if the
*member check* succeeds, i.e. the writing principal's tenant is exactly the tenant
owning the target resource.  Otherwise the request is dropped and the store is
unchanged. -/

/-- Tenant identifiers. -/
abbrev TenantId := Nat
/-- Principal (user / service account) identifiers. -/
abbrev PrincipalId := Nat
/-- Resource (record) identifiers. -/
abbrev ResourceId := Nat
/-- Values stored in resources. -/
abbrev Value := Nat

/-- The static environment: the tenant of each principal, and the owning tenant of
each resource. -/
structure Env where
  /-- The tenant a principal belongs to. -/
  tenantOf : PrincipalId → TenantId
  /-- The tenant owning a resource. -/
  ownerOf : ResourceId → TenantId

/-- A write request: a principal asks to store `value` into `resource`. -/
structure Request where
  /-- The requesting principal. -/
  principal : PrincipalId
  /-- The targeted resource. -/
  resource : ResourceId
  /-- The value to be written. -/
  value : Value

/-- The store maps every resource to its current value. -/
abbrev Store := ResourceId → Value

/-- The membership guard of the isolation engine: the principal's tenant must own
the targeted resource. -/

theorem demo_in_tenant_write_succeeds :
    run demoEnv emptyStore [{ principal := 1, resource := 1, value := 7 }] 1 = 7 := by
  decide

end WriteIntegrity
end PCA

