/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, and Lean 4
requires `import` commands to precede every other command in a file.  The
development below is therefore kept self-contained in core Lean 4, with no
imports.  The only external ingredient it would otherwise need is Mathlib's
`Function.update_of_ne` (`Mathlib/Logic/Function/Basic.lean`), whose role is
played here by `Store.write_apply_of_ne`, proved directly from `if_neg`.
-/

namespace PCA.WriteIntegrity

/-- A principal acting on the store, described by its tenant memberships:
`tenants t = true` means the principal is a member of tenant `t`. -/
structure Principal (Tenant : Type u) where
  /-- Decidable membership predicate: the tenants this principal belongs to. -/
  tenants : Tenant → Bool

/-- A multi-tenant store: a total contents map together with an ownership
labelling assigning to each key the tenant that owns it. -/
structure Store (Tenant : Type u) (Key : Type v) (Value : Type w) where
  /-- Contents of the store. -/
  data : Key → Value
  /-- The tenant owning each key. -/
  owner : Key → Tenant

namespace Store

variable {Tenant : Type u} {Key : Type v} {Value : Type w} [DecidableEq Key]

/-- Unconditional (unguarded) write of `v` at key `k`; ownership is unchanged. -/

theorem member_check_prevents_cross_tenant_write_list (p : Principal Tenant)
    (ops : List (Key × Value)) (s : Store Tenant Key Value) (k' : Key)
    (hk' : p.tenants (s.owner k') = false) :
    (ops.foldl (fun t op => guardedWrite p t op.1 op.2) s).data k' = s.data k' := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      have howner : (guardedWrite p s op.1 op.2).owner = s.owner :=
        guardedWrite_owner p s op.1 op.2
      have hk'' : p.tenants ((guardedWrite p s op.1 op.2).owner k') = false := by
        rw [howner]; exact hk'
      calc (List.foldl (fun t op => guardedWrite p t op.1 op.2)
              (guardedWrite p s op.1 op.2) ops).data k'
          = (guardedWrite p s op.1 op.2).data k' := ih _ hk''
        _ = s.data k' := member_check_prevents_cross_tenant_write p s op.1 op.2 k' hk'

end PCA.WriteIntegrity

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

