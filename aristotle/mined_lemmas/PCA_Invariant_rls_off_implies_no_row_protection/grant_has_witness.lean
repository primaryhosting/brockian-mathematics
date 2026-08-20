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

theorem grant_has_witness {t : Table} {s : Subject} {r : Row}
    (hrls : t.rls = true) (hex : t.subjectExempt s = false)
    (h : Engine.visible t s r = true) :
    ∃ p ∈ t.policies, p.appliesTo s = true ∧ p.predicate r = true := by
  rcases Engine.sound h with h' | h' | h'
  · exact absurd h' (by simp [hrls])
  · exact absurd h' (by simp [hex])
  · exact h'

end Invariant

end PCA

#print axioms PCA.Invariant.rls_off_implies_no_row_protection
#print axioms PCA.Engine.visible_iff_allowed
#print axioms PCA.Invariant.forced_rls_no_policies_protects
#print axioms PCA.Invariant.grant_has_witness

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

