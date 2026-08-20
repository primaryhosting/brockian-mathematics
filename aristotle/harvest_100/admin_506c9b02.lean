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
def Policy.appliesTo (pol : Policy) (t : Table) (p : Principal) : Bool :=
  (pol.table == t.id) && pol.roles.contains p.role

/-- Visibility of a row `r` of table `t` to principal `p` under engine `e`.

This mirrors the standard RLS evaluation order:
* if RLS is disabled on the table, every row is visible;
* a `BYPASSRLS` principal sees every row;
* the table owner sees every row unless `FORCE ROW LEVEL SECURITY` is set;
* otherwise the row is visible iff some applicable permissive policy accepts it and
  every applicable restrictive policy accepts it. -/
def Engine.visible (e : Engine) (t : Table) (p : Principal) (r : Row) : Bool :=
  if !t.rlsEnabled then true
  else if p.bypassRLS then true
  else if (p.role == t.owner) && !t.rlsForced then true
  else
    (e.policies.any fun pol => pol.appliesTo t p && pol.permissive && pol.pred r) &&
    (e.policies.all fun pol => !pol.appliesTo t p || pol.permissive || pol.pred r)

/-- A row is *protected* when some principal is denied access to it. -/
def Engine.rowProtected (e : Engine) (t : Table) (r : Row) : Prop :=
  ∃ p : Principal, e.visible t p r = false

namespace Invariant

/-- **Soundness of the isolation model.** If row-level security is switched off on a
table, then no row of that table enjoys any protection: every principal sees every row,
hence no row is protected. -/
theorem rls_off_implies_no_row_protection
    (e : Engine) (t : Table) (r : Row) (h : t.rlsEnabled = false) :
    ¬ e.rowProtected t r := by
  rintro ⟨p, hp⟩
  simp [Engine.visible, h] at hp

/-- Every principal sees every row when RLS is off (the strengthened form of the
invariant above). -/
theorem visible_of_rls_off
    (e : Engine) (t : Table) (p : Principal) (r : Row) (h : t.rlsEnabled = false) :
    e.visible t p r = true := by
  simp [Engine.visible, h]

/-- **Completeness (sharpness) of the invariant.** The hypothesis cannot be dropped:
when RLS is enabled and forced and no policy is installed, every row is protected. -/
theorem rowProtected_of_rls_on_no_policies
    (e : Engine) (t : Table) (r : Row)
    (hOn : t.rlsEnabled = true) (hForced : t.rlsForced = true)
    (hPol : e.policies = []) :
    e.rowProtected t r :=
  ⟨⟨t.owner, false⟩, by simp [Engine.visible, hOn, hForced, hPol]⟩

end Invariant

end PCA

