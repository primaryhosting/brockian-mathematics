import Mathlib

/-!
# A formal model of the PCA isolation engine (row-level security)

This file develops a small, fully formal model of the row-isolation ("row level
security", RLS) engine of the PCA system, together with

* a *declarative specification* `PCA.Spec.Allowed` describing when a subject is
  entitled to see a row,
* an *executable engine* `PCA.Engine.visible` implementing the access decision,
* **soundness** (`PCA.Engine.sound`) and **completeness** (`PCA.Engine.complete`)
  of the engine with respect to the specification, and
* the main invariant
  `PCA.Invariant.rls_off_implies_no_row_protection`: if row level security is
  switched off on a table, then no row of that table is protected, i.e. every
  subject can see every row.
-/

namespace PCA

/-- Identifier of a role (a database principal). -/
abbrev RoleId := Nat

/-- Identifier of a row. -/
abbrev RowId := Nat

/-- A row of a table: its identity, its owning role and its tenant. -/
structure Row where
  id : RowId
  owner : RoleId
  tenant : Nat
  deriving DecidableEq, Repr

/-- A row level security policy: it applies to a set of roles (the empty list
meaning "all roles") and carries a `USING`-style predicate on rows. -/
structure Policy where
  name : String
  roles : List RoleId
  predicate : Row → Bool

/-- A table: whether RLS is enabled, whether it is *forced* (so that the table
owner is not exempt), the owning role, and the list of attached policies. -/
structure Table where
  rls : Bool
  forceRls : Bool
  owner : RoleId
  policies : List Policy

/-- A subject performing an access: its role and whether it holds the
`BYPASSRLS` attribute. -/
structure Subject where
  role : RoleId
  bypassRls : Bool
  deriving DecidableEq, Repr

/-- A policy applies to a subject when its role list is empty (all roles) or
mentions the subject's role. -/

theorem forced_rls_no_policies_protects {t : Table} (hrls : t.rls = true)
    (hforce : t.forceRls = true) (hpol : t.policies = []) (r : Row) :
    RowProtected t r := by
  refine ⟨⟨t.owner, false⟩, ?_⟩
  simp [Engine.visible, Table.subjectExempt, hrls, hforce, hpol]

/-- No fabrication of access: whenever the engine grants a non-exempt subject
access to a row under enabled RLS, an actual policy justifies it. -/
