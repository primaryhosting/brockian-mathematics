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
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

universe u v w x

/-- A tenancy policy for the isolation engine: every resource belongs to exactly
one tenant, and each principal is a member of some collection of tenants. -/
structure Policy (Principal : Type u) (Resource : Type v) (Tenant : Type w) where
  /-- The (unique) tenant owning a given resource. -/
  tenantOf : Resource → Tenant
  /-- Membership relation between principals and tenants. -/
  member : Principal → Tenant → Prop

/-- A write request: a principal asking to store `value` at `target`. -/
structure Write (Principal : Type u) (Resource : Type v) (Value : Type x) where
  /-- The principal issuing the write. -/
  actor : Principal
  /-- The resource being written. -/
  target : Resource
  /-- The value to be written. -/
  value : Value

variable {Principal : Type u} {Resource : Type v} {Tenant : Type w} {Value : Type x}

/-- Point update of a store, i.e. `Function.update` specialised to the
non-dependent stores used here (kept local so that this module is
dependency-free; it agrees with `Function.update` from Mathlib). -/

noncomputable def update (st : Resource → Value) (a : Resource) (v : Value) :
    Resource → Value :=
  open Classical in
  fun r => if r = a then v else st r

@[simp]
