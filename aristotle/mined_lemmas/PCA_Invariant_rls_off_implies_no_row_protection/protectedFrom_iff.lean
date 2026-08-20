/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

/-! ## Model of the row-level isolation engine

We model a database table equipped with a row-level security (RLS) configuration.

* `Principal` is the type of acting identities (users, roles, service accounts).
* `Row` is the type of rows stored in the table.

A *row security policy* consists of a predicate saying to which principals it
applies (`appliesTo`), and, for those principals, which rows it lets through
(`permits`).  A table carries a boolean flag `rlsEnabled` together with the list
of policies attached to it.

The engine's visibility semantics is the standard one: when the flag is off the
policies are *not consulted at all* and every row is returned; when the flag is
on a row is returned only if some applicable policy permits it.

Everything below is stated for arbitrary types of principals and rows and for an
arbitrary policy set, so the invariant holds for every configuration of the
engine. -/

universe u v

/-- A row security policy: which principals it governs, and which rows it lets
through for such a principal. -/
structure RowPolicy (Principal : Type u) (Row : Type v) where
  /-- The principals governed by this policy. -/
  appliesTo : Principal → Prop
  /-- For a governed principal, the rows this policy permits. -/
  permits : Principal → Row → Prop

/-- A table together with its row-level-security configuration. -/
structure Table (Principal : Type u) (Row : Type v) where
  /-- Whether row level security is enabled on the table. -/
  rlsEnabled : Bool
  /-- The row security policies attached to the table. -/
  policies : List (RowPolicy Principal Row)

variable {Principal : Type u} {Row : Type v}

/-- Some attached policy governs `p` and permits the row `r`. -/

theorem protectedFrom_iff {Principal : Type u} {Row : Type v}
    (t : Table Principal Row) (p : Principal) (r : Row) :
    t.protectedFrom p r ↔ t.rlsEnabled = true ∧ ¬ t.somePolicyPermits p r := by
  show ¬ (if t.rlsEnabled = true then t.somePolicyPermits p r else True) ↔ _
  cases hb : t.rlsEnabled <;> simp

/-- Operational consequence for query evaluation: with RLS off, filtering a list
of rows through the engine's visibility check removes nothing. -/
