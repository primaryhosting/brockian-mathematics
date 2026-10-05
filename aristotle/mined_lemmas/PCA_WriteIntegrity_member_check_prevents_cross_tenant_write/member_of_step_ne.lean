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

theorem member_of_step_ne [DecidableEq Res] {pol : Policy Tenant User Res}
    {req : Request User Res Val} {st : Store Res Val} {res : Res}
    (h : step pol req st res ≠ st res) :
    res = req.target ∧ pol.member req.actor (pol.tenantOf res) = true := by
  cases hauth : authorized pol req with
  | false =>
      exact absurd (congrFun (step_of_not_authorized st hauth) res) h
  | true =>
      rw [step_of_authorized st hauth] at h
      by_cases hres : res = req.target
      · subst hres
        exact ⟨rfl, hauth⟩
      · exact absurd (upd_of_ne st _ hres) h

/-- **Single-step isolation.** If the actor of a request fails the member check for the
tenant owning a resource `res`, then the engine leaves `res` untouched: the member check
prevents any cross-tenant write. -/
