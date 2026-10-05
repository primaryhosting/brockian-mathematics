/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Invariant

/-! ## The model of the row-isolation engine

We model the row-level-security (RLS) fragment of an isolation engine in the style of a
relational database: a table carries a *row security* switch, a *force* switch, an owner,
and a list of row policies.  A read of a row by a role is permitted unless row security is
*active* for that role on that table and the attached policies reject the row.
-/

/-- A row of a table: an identifier together with the data used by policy predicates. -/
structure Row where
  id : Nat
  tenant : Nat
  owner : String
  deriving DecidableEq, Repr

/-- A database role. `bypassRls` models the `BYPASSRLS` attribute, `superuser` the
superuser attribute; both make row security inactive. -/
structure Role where
  name : String
  bypassRls : Bool
  superuser : Bool
  deriving DecidableEq, Repr

/-- The command a policy applies to. -/
inductive Cmd
  | select | insert | update | delete
  deriving DecidableEq, Repr

/-- A row policy: the command it governs, whether it is permissive (as opposed to
restrictive), the roles it applies to (an empty list means `PUBLIC`), and its predicate. -/
structure Policy where
  cmd : Cmd
  permissive : Bool
  roles : List String
  pred : Role → Row → Bool

/-- A table: the row-security switch, the force switch, the owning role's name, and the
list of attached row policies. -/
structure Table where
  rls : Bool
  forceRls : Bool
  owner : String
  policies : List Policy

/-- A policy applies to a role when its role list is `PUBLIC` or mentions the role. -/
def Policy.appliesTo (p : Policy) (r : Role) : Bool :=
  p.roles.isEmpty || p.roles.contains r.name

/-- Row security is *active* for a role on a table exactly when the switch is on, the role
is neither a superuser nor `BYPASSRLS`, and the role is not the (unforced) table owner. -/
def Table.rlsActive (t : Table) (r : Role) : Bool :=
  t.rls && !r.bypassRls && !r.superuser && (t.forceRls || (r.name != t.owner))

/-- The permissive policies of `t` governing command `c` and applicable to role `r`. -/
def Table.permissiveFor (t : Table) (c : Cmd) (r : Role) : List Policy :=
  t.policies.filter (fun p => p.permissive && p.cmd == c && p.appliesTo r)

/-- The restrictive policies of `t` governing command `c` and applicable to role `r`. -/
def Table.restrictiveFor (t : Table) (c : Cmd) (r : Role) : List Policy :=
  t.policies.filter (fun p => !p.permissive && p.cmd == c && p.appliesTo r)

/-- The decision procedure of the isolation engine: role `r` may access `row` of table `t`
under command `c` iff row security is inactive, or some applicable permissive policy admits
the row and every applicable restrictive policy admits it. -/
def Table.permits (t : Table) (c : Cmd) (r : Role) (row : Row) : Bool :=
  if t.rlsActive r then
    (t.permissiveFor c r).any (fun p => p.pred r row) &&
      (t.restrictiveFor c r).all (fun p => p.pred r row)
  else
    true

/-- A table *protects a row* when there is some command, role and row that the engine
denies.  This is the observable content of "row protection". -/
def Table.protectsSomeRow (t : Table) : Prop :=
  ∃ (c : Cmd) (r : Role) (row : Row), t.permits c r row = false

/-! ## Soundness: switching row security off removes all row protection -/

/-- If the row-security switch of a table is off, row security is never active. -/
theorem rlsActive_eq_false_of_rls_off {t : Table} (h : t.rls = false) (r : Role) :
    t.rlsActive r = false := by
  simp [Table.rlsActive, h]

/-- **Target theorem.**  If row-level security is switched off on a table, the isolation
engine grants every access: no row of the table is protected, for any command, any role and
any row, no matter which policies are attached to the table. -/
theorem rls_off_implies_no_row_protection {t : Table} (h : t.rls = false) :
    (∀ (c : Cmd) (r : Role) (row : Row), t.permits c r row = true) ∧
      ¬ t.protectsSomeRow := by
  have hgrant : ∀ (c : Cmd) (r : Role) (row : Row), t.permits c r row = true := by
    intro c r row
    simp [Table.permits, rlsActive_eq_false_of_rls_off h]
  refine ⟨hgrant, ?_⟩
  rintro ⟨c, r, row, hden⟩
  rw [hgrant c r row] at hden
  exact Bool.noConfusion hden

/-- With row security off the decision does not depend on the attached policies at all:
any two tables that differ only in their policy lists behave identically. -/
theorem permits_indep_of_policies {t t' : Table} (h : t.rls = false) (h' : t'.rls = false)
    (c : Cmd) (r : Role) (row : Row) :
    t.permits c r row = t'.permits c r row := by
  simp [Table.permits, rlsActive_eq_false_of_rls_off h, rlsActive_eq_false_of_rls_off h']

/-! ## Completeness: the invariant is sharp

Row security being off is not merely sufficient but exactly the condition that is needed:
whenever it is on there is a policy configuration exhibiting genuine row protection, and
conversely any protection witnesses that the switch is on. -/

/-- Any observed denial forces the row-security switch to be on: the engine never denies
access on a table whose row security is off. -/
theorem rls_on_of_protectsSomeRow {t : Table} (h : t.protectsSomeRow) : t.rls = true := by
  rcases Bool.eq_false_or_eq_true t.rls with h1 | h0
  · exact h1
  · exact absurd h (rls_off_implies_no_row_protection h0).2

/-- Sharpness: for every table whose row-security switch is on there is a table with the
same switches and owner (differing only in its policies) that really does protect a row. -/
theorem exists_protection_of_rls_on {t : Table} (h : t.rls = true) :
    ∃ t' : Table, t'.rls = t.rls ∧ t'.forceRls = true ∧ t'.owner = t.owner ∧
      t'.protectsSomeRow := by
  refine ⟨⟨t.rls, true, t.owner, []⟩, rfl, rfl, rfl, ?_⟩
  refine ⟨Cmd.select, ⟨"alice", false, false⟩, ⟨0, 0, "alice"⟩, ?_⟩
  simp [Table.permits, Table.rlsActive, Table.permissiveFor, Table.restrictiveFor, h]

/-- Combining both directions: a table protects some row **iff** row security is on and
the policies deny some access. -/
theorem protectsSomeRow_iff {t : Table} :
    t.protectsSomeRow ↔ t.rls = true ∧ t.protectsSomeRow :=
  ⟨fun h => ⟨rls_on_of_protectsSomeRow h, h⟩, fun h => h.2⟩

end Invariant
end PCA

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

