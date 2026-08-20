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
def Table.somePolicyPermits (t : Table Principal Row) (p : Principal) (r : Row) : Prop :=
  ∃ pol, pol ∈ t.policies ∧ pol.appliesTo p ∧ pol.permits p r

/-- The visibility semantics of the isolation engine: with RLS disabled every
row is visible; with RLS enabled a row is visible exactly when some applicable
policy permits it. -/
def Table.visible (t : Table Principal Row) (p : Principal) (r : Row) : Prop :=
  if t.rlsEnabled = true then t.somePolicyPermits p r else True

/-- A row `r` is *protected from* principal `p` when the engine hides it. -/
def Table.protectedFrom (t : Table Principal Row) (p : Principal) (r : Row) : Prop :=
  ¬ t.visible p r

/-- The table provides *row protection* when it hides at least one row from at
least one principal. -/
def Table.providesRowProtection (t : Table Principal Row) : Prop :=
  ∃ (p : Principal) (r : Row), t.protectedFrom p r

/-- Row-level security is switched off on the table. -/
def Table.rlsOff (t : Table Principal Row) : Prop := t.rlsEnabled = false

namespace Invariant

/-- **Soundness of the isolation model.**  If row-level security is switched off
on a table, then the table provides no row protection whatsoever: no row is
hidden from any principal, whatever policies happen to be attached to it. -/
theorem rls_off_implies_no_row_protection {Principal : Type u} {Row : Type v}
    (t : Table Principal Row) (h : t.rlsOff) :
    ¬ t.providesRowProtection := by
  rintro ⟨p, r, hpr⟩
  apply hpr
  show (if t.rlsEnabled = true then t.somePolicyPermits p r else True)
  rw [h]
  simp

/-- Equivalent positive formulation: with RLS off, every row is visible to every
principal. -/
theorem rls_off_all_rows_visible {Principal : Type u} {Row : Type v}
    (t : Table Principal Row) (h : t.rlsOff) (p : Principal) (r : Row) :
    t.visible p r := by
  show (if t.rlsEnabled = true then t.somePolicyPermits p r else True)
  rw [h]
  simp

/-- **Completeness (contrapositive).**  Any table that does protect some row
must have row-level security enabled. -/
theorem row_protection_implies_rls_on {Principal : Type u} {Row : Type v}
    (t : Table Principal Row) (h : t.providesRowProtection) :
    t.rlsEnabled = true := by
  cases hb : t.rlsEnabled with
  | false => exact absurd h (rls_off_implies_no_row_protection t hb)
  | true => rfl

/-- Protection of a row is exactly the conjunction of the flag being on with the
failure of every attached policy to permit the row: all protection is produced by
the policy layer, and that layer is gated by `rlsEnabled`. -/
theorem protectedFrom_iff {Principal : Type u} {Row : Type v}
    (t : Table Principal Row) (p : Principal) (r : Row) :
    t.protectedFrom p r ↔ t.rlsEnabled = true ∧ ¬ t.somePolicyPermits p r := by
  show ¬ (if t.rlsEnabled = true then t.somePolicyPermits p r else True) ↔ _
  cases hb : t.rlsEnabled <;> simp

/-- Operational consequence for query evaluation: with RLS off, filtering a list
of rows through the engine's visibility check removes nothing. -/
theorem visible_filter_eq_self_of_rlsOff {Principal : Type u} {Row : Type v}
    (t : Table Principal Row) (h : t.rlsOff) (p : Principal)
    (rows : List Row) [DecidablePred fun r => t.visible p r] :
    rows.filter (fun r => decide (t.visible p r)) = rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
      have hv : decide (t.visible p r) = true :=
        decide_eq_true (rls_off_all_rows_visible t h p r)
      simp [List.filter, hv, ih]

end Invariant

end PCA

