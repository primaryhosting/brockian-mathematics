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

theorem step_change_imp_member (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (req : Request Principal Resource Value)
    (r : Resource) (h : step E σ req r ≠ σ r) :
    req.resource = r ∧ Authorized E req ∧ E.member req.principal (E.tenantOf r) := by
  unfold step at h
  by_cases hauth : Authorized E req
  · rw [if_pos hauth] at h
    by_cases hr : req.resource = r
    · subst hr
      exact ⟨rfl, hauth, hauth⟩
    · -- `Function.update_of_ne` : updating at a different point leaves the value alone
      exact absurd (Function.update_of_ne (Ne.symm hr) _ _) h
  · rw [if_neg hauth] at h
    exact absurd rfl h

/-- A step performed by a principal that is *not* a member of tenant `t` leaves
every resource of tenant `t` untouched. -/
