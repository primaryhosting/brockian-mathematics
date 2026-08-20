/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires `import` commands to precede every other command,
including module documentation, so the mandated header above rules out an
`import Mathlib` line.  The development below therefore only uses Lean core.
The one Mathlib fact it needs is the pointwise-update lemma
`Function.update_of_ne : a ≠ b → Function.update f b v a = f a`; it is reproved
here for the local `PCA.WriteIntegrity.upd` as `upd_of_ne`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

/-! ## The isolation model

A multi-tenant store maps resource identifiers to records.  Every stored record
carries the tenant that owns it together with a payload.  A write request names
a principal, a resource, the tenant under which the principal claims to act, and
the payload to be stored.

The *reference monitor* accepts a request only when

* the principal is a member of the tenant it claims to act for, and
* if the resource already exists, it is owned by exactly that tenant.

The main theorem states that under this guard no write can ever touch a record
owned by a tenant the acting principal does not belong to. -/

universe u v w z

variable {Res : Type u} {Tenant : Type v} {Prin : Type w} {Val : Type z}

/-- A stored record: the owning tenant together with the payload. -/
structure Record (Tenant : Type v) (Val : Type z) where
  /-- The tenant owning the record. -/
  tenant : Tenant
  /-- The stored payload. -/
  value : Val

/-- A store maps resource identifiers to records (`none` = the resource is absent). -/
abbrev Store (Res : Type u) (Tenant : Type v) (Val : Type z) := Res → Option (Record Tenant Val)

/-- A write request. -/
structure WriteReq (Res : Type u) (Tenant : Type v) (Prin : Type w) (Val : Type z) where
  /-- The principal issuing the write. -/
  principal : Prin
  /-- The tenant the principal claims to act for. -/
  tenant : Tenant
  /-- The resource to be written. -/
  resource : Res
  /-- The payload to be written. -/
  value : Val

/-- The membership relation of the isolation engine: `mem p t` means principal
`p` belongs to tenant `t`. -/
abbrev Memberships (Prin : Type w) (Tenant : Type v) := Prin → Tenant → Prop

/-- Pointwise update of a store at a single resource. -/

theorem foldl_step_preserves_foreign [DecidableEq Res]
    (mem : Memberships Prin Tenant) (x : Res) (rec : Record Tenant Val) :
    ∀ (rs : List (WriteReq Res Tenant Prin Val)) (st : Store Res Tenant Val),
      st x = some rec → (∀ r ∈ rs, ¬ mem r.principal rec.tenant) →
      (rs.foldl (step mem) st) x = some rec := by
  intro rs
  induction rs with
  | nil => intro st h _; simpa using h
  | cons r rs ih =>
      intro st h hall
      refine ih (step mem st r) ?_ (fun q hq => hall q (List.mem_cons_of_mem _ hq))
      exact foreign_owner_stable mem st r x rec h (hall r (List.mem_cons_self ..))

/-- Authorized writes do take effect: the guard is not vacuously restrictive. -/
