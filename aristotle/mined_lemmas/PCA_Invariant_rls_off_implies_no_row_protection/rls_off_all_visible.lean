/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v

namespace PCA

/-- A row-level-security policy, in the style of a PostgreSQL `CREATE POLICY`
statement: it names the roles it applies to (`appliesTo`) and carries a `USING`
predicate that a row must satisfy for the policy to grant visibility. -/
structure Policy (Role : Type u) (Row : Type v) where
  /-- Roles this policy is declared `TO`. -/
  appliesTo : Role → Bool
  /-- The `USING` clause: which rows the policy exposes. -/
  usingCheck : Row → Bool

/-- A table together with its isolation configuration: whether row-level
security is enabled, whether it is *forced* (so that the table owner is not
exempt), who owns the table, and the list of permissive policies attached. -/
structure Table (Role : Type u) (Row : Type v) where
  /-- `ALTER TABLE ... ENABLE ROW LEVEL SECURITY`. -/
  rlsEnabled : Bool
  /-- `ALTER TABLE ... FORCE ROW LEVEL SECURITY`. -/
  forceRls : Bool
  /-- The owner of the table. -/
  owner : Role
  /-- The permissive policies attached to the table. -/
  policies : List (Policy Role Row)

variable {Role : Type u} {Row : Type v} [DecidableEq Role]

/-- The visibility semantics of the isolation engine: a row is visible to a
role when row-level security is off, or the role is an exempt owner, or some
permissive policy applicable to the role admits the row. -/

theorem rls_off_all_visible
    (t : Table Role Row) (h : t.rlsEnabled = false) (role : Role) (r : Row) :
    t.visible role r = true := by
  simp [Table.visible, h]

/-- Consequence for queries: with row-level security off, a query filters
nothing away. -/
