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

variable {Tenant : Type u} {User : Type v} {Res : Type w} {Val : Type x}

/-- A store maps each resource to its current value. -/
abbrev Store (Res : Type w) (Val : Type x) : Type (max w x) := Res → Val

/-- Pointwise update of a store. -/

theorem step_eq_of_not_member [DecidableEq Res] {pol : Policy Tenant User Res}
    {req : Request User Res Val} (st : Store Res Val) {res : Res}
    (h : pol.member req.actor (pol.tenantOf res) = false) :
    step pol req st res = st res := by
  cases hauth : authorized pol req with
  | false => exact congrFun (step_of_not_authorized st hauth) res
  | true =>
      rw [step_of_authorized st hauth]
      have hres : res ≠ req.target := by
        intro hEq
        subst hEq
        rw [authorized, h] at hauth
        exact Bool.noConfusion hauth
      exact upd_of_ne st _ hres

/-- **Main theorem (write integrity / tenant isolation).**

Consider a trace of write requests processed by the engine, and a resource `res`.
If *no* actor occurring in the trace passes the member check for the tenant that owns
`res`, then the value stored at `res` is unchanged by the whole trace.

In other words, the member check performed by the guard is sufficient to rule out every
cross-tenant write: a user can only ever affect resources belonging to tenants it is a
member of. -/
