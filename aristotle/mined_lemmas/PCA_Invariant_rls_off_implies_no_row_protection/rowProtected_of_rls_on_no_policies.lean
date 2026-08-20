/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
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

/-! ## A model of the row-level-security (RLS) isolation engine -/

/-- Identifier of a database role (a principal's identity). -/
abbrev RoleId := Nat

/-- Identifier of a table. -/
abbrev TableId := Nat

/-- A row of some table, carrying its owning role (used by ownership policies). -/
structure Row where
  /-- Row identifier. -/
  id : Nat
  /-- The table this row belongs to. -/
  table : TableId
  /-- The role that owns this row. -/
  owner : RoleId
  deriving DecidableEq, Repr

/-- A row-level security policy: it targets one table, applies to a list of roles,
is either *permissive* (grants access when its predicate holds) or *restrictive*
(denies access when its predicate fails), and is given by a boolean predicate on rows. -/
structure Policy where
  /-- The table the policy is attached to. -/
  table : TableId
  /-- The roles the policy applies to. -/
  roles : List RoleId
  /-- `true` for a permissive policy, `false` for a restrictive one. -/
  permissive : Bool
  /-- The `USING` predicate of the policy. -/
  pred : Row → Bool

/-- A principal issuing a query: a role, possibly with the `BYPASSRLS` attribute. -/
structure Principal where
  /-- The role the principal acts as. -/
  role : RoleId
  /-- Whether the principal has the `BYPASSRLS` attribute. -/
  bypassRLS : Bool
  deriving DecidableEq, Repr

/-- A table together with its RLS configuration. -/
structure Table where
  /-- Table identifier. -/
  id : TableId
  /-- Whether `ROW LEVEL SECURITY` is enabled on the table. -/
  rlsEnabled : Bool
  /-- Whether `FORCE ROW LEVEL SECURITY` is set (so the owner is not exempt). -/
  rlsForced : Bool
  /-- The role owning the table. -/
  owner : RoleId
  deriving DecidableEq, Repr

/-- The isolation engine state: the set of policies currently installed. -/
structure Engine where
  /-- All installed policies, for all tables. -/
  policies : List Policy

/-- A policy is *applicable* to a principal querying a table when it is attached to that
table and lists the principal's role. -/

theorem rowProtected_of_rls_on_no_policies
    (e : Engine) (t : Table) (r : Row)
    (hOn : t.rlsEnabled = true) (hForced : t.rlsForced = true)
    (hPol : e.policies = []) :
    e.rowProtected t r :=
  ⟨⟨t.owner, false⟩, by simp [Engine.visible, hOn, hForced, hPol]⟩

end Invariant

end PCA

