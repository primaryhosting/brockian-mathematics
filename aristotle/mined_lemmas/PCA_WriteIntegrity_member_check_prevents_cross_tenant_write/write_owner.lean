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

@[simp] theorem write_owner (s : Store Tenant Key Value) (k : Key) (v : Value) :
    (s.write k v).owner = s.owner := rfl

end Store

variable {Tenant : Type u} {Key : Type v} {Value : Type w} [DecidableEq Key]

/-- The membership check performed by the isolation engine before a write: the
principal must be a member of the tenant that owns the target key. -/
