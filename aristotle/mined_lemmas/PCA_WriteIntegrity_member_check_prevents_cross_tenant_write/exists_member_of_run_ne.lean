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

theorem exists_member_of_run_ne [DecidableEq Res]
    (pol : Policy Tenant User Res) (trace : List (Request User Res Val))
    (st : Store Res Val) (res : Res)
    (h : run pol trace st res ≠ st res) :
    ∃ req ∈ trace, pol.member req.actor (pol.tenantOf res) = true := by
  refine Classical.byContradiction (fun hcon => h ?_)
  refine member_check_prevents_cross_tenant_write pol trace st res (fun req hreq => ?_)
  cases hm : pol.member req.actor (pol.tenantOf res) with
  | false => rfl
  | true => exact absurd ⟨req, hreq, hm⟩ hcon

/-- **Completeness of the guard (no over-blocking).** A request issued by a genuine
member of the tenant owning the target does take effect. -/
