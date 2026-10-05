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

theorem exists_protection_of_rls_on {t : Table} (h : t.rls = true) :
    ∃ t' : Table, t'.rls = t.rls ∧ t'.forceRls = true ∧ t'.owner = t.owner ∧
      t'.protectsSomeRow := by
  refine ⟨⟨t.rls, true, t.owner, []⟩, rfl, rfl, rfl, ?_⟩
  refine ⟨Cmd.select, ⟨"alice", false, false⟩, ⟨0, 0, "alice"⟩, ?_⟩
  simp [Table.permits, Table.rlsActive, Table.permissiveFor, Table.restrictiveFor, h]

/-- Combining both directions: a table protects some row **iff** row security is on and
the policies deny some access. -/
