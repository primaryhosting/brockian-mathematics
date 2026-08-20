import Mathlib

/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA
namespace WriteIntegrity

universe u v w x

/-- A write request: a principal asks to store `value` at `resource`. -/
structure Request (Principal : Type u) (Resource : Type v) (Value : Type w) where
  /-- The principal issuing the write. -/
  principal : Principal
  /-- The resource being written to. -/
  resource : Resource
  /-- The value to be written. -/
  value : Value

/-- The isolation environment: every resource belongs to exactly one tenant, and
`member p t` says that principal `p` is a member of tenant `t`. -/
structure Env (Tenant : Type x) (Principal : Type u) (Resource : Type v) where
  /-- The (unique) tenant owning a resource. -/
  tenantOf : Resource → Tenant
  /-- Tenant membership relation for principals. -/
  member : Principal → Tenant → Prop

variable {Tenant : Type x} {Principal : Type u} {Resource : Type v} {Value : Type w}

/-- The guard used by the engine: a write is authorized exactly when the issuing
principal is a member of the tenant owning the target resource. -/

@[simp] theorem exec_cons (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (req : Request Principal Resource Value)
    (rest : List (Request Principal Resource Value)) :
    exec E σ (req :: rest) = exec E (step E σ req) rest := rfl

/-- **Soundness of the guard (one step).** If a single step changes the stored
value at some resource `r`, then the request was authorized, targeted `r`, and
hence its issuer is a member of the tenant owning `r`. -/
