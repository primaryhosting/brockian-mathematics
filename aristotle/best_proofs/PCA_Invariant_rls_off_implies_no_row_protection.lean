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
def Policy.appliesTo (p : Policy) (s : Subject) : Bool :=
  p.roles.isEmpty || p.roles.contains s.role

/-- A subject is exempt from the policies of a table when it can bypass RLS, or
when it owns the table and RLS is not forced. -/
def Table.subjectExempt (t : Table) (s : Subject) : Bool :=
  s.bypassRls || (decide (s.role = t.owner) && !t.forceRls)

namespace Engine

/-- The access decision of the isolation engine: with RLS off everything is
visible; otherwise exempt subjects see everything and all other subjects see
exactly the rows admitted by some applicable policy. -/
def visible (t : Table) (s : Subject) (r : Row) : Bool :=
  if !t.rls then true
  else if t.subjectExempt s then true
  else t.policies.any (fun p => p.appliesTo s && p.predicate r)

end Engine

namespace Spec

/-- The declarative specification of the isolation model: a subject may see a
row iff RLS is off, or the subject is exempt, or some applicable policy admits
the row. -/
def Allowed (t : Table) (s : Subject) (r : Row) : Prop :=
  t.rls = false ∨ t.subjectExempt s = true ∨
    ∃ p ∈ t.policies, p.appliesTo s = true ∧ p.predicate r = true

end Spec

namespace Engine

/-- **Soundness**: every access granted by the engine is allowed by the
specification. -/
theorem sound {t : Table} {s : Subject} {r : Row}
    (h : visible t s r = true) : Spec.Allowed t s r := by
  unfold visible at h
  by_cases hrls : t.rls
  · simp only [hrls, Bool.not_true] at h
    by_cases hex : t.subjectExempt s
    · exact Or.inr (Or.inl hex)
    · simp only [hex] at h
      refine Or.inr (Or.inr ?_)
      obtain ⟨p, hp, hp'⟩ := List.any_eq_true.mp h
      exact ⟨p, hp, by simpa using hp'⟩
  · exact Or.inl (by simpa using hrls)

/-- **Completeness**: every access allowed by the specification is granted by
the engine. -/
theorem complete {t : Table} {s : Subject} {r : Row}
    (h : Spec.Allowed t s r) : visible t s r = true := by
  unfold visible
  rcases h with h | h | ⟨p, hp, hps, hpr⟩
  · simp [h]
  · simp [h]
  · by_cases hrls : t.rls
    · simp only [hrls, Bool.not_true]
      by_cases hex : t.subjectExempt s
      · simp [hex]
      · simp only [hex]
        exact List.any_eq_true.mpr ⟨p, hp, by simp [hps, hpr]⟩
    · simp [hrls]

/-- The engine decision is exactly the specification. -/
theorem visible_iff_allowed (t : Table) (s : Subject) (r : Row) :
    visible t s r = true ↔ Spec.Allowed t s r :=
  ⟨sound, complete⟩

end Engine

/-- A row is *protected* in a table when some subject is denied access to it. -/
def RowProtected (t : Table) (r : Row) : Prop :=
  ∃ s : Subject, Engine.visible t s r = false

namespace Invariant

/-- **Main invariant.** If row level security is switched off on a table, then
no row of the table is protected: the isolation engine grants every subject
access to every row. -/
theorem rls_off_implies_no_row_protection {t : Table} (h : t.rls = false) :
    ∀ r : Row, ¬ RowProtected t r := by
  rintro r ⟨s, hs⟩
  rw [Engine.visible, h] at hs
  simp at hs

/-- Contrapositive form: a protected row witnesses that RLS is enabled. -/
theorem row_protected_implies_rls_on {t : Table} {r : Row}
    (h : RowProtected t r) : t.rls = true := by
  by_contra hc
  exact rls_off_implies_no_row_protection (by simpa using hc) r h

/-- With RLS off the specification allows every access, so the model itself
(not merely its implementation) provides no isolation. -/
theorem rls_off_allows_all {t : Table} (h : t.rls = false) (s : Subject) (r : Row) :
    Spec.Allowed t s r := Or.inl h

/-- Conversely, a table with forced RLS and no policies protects every row:
any subject without `BYPASSRLS` is denied. -/
theorem forced_rls_no_policies_protects {t : Table} (hrls : t.rls = true)
    (hforce : t.forceRls = true) (hpol : t.policies = []) (r : Row) :
    RowProtected t r := by
  refine ⟨⟨t.owner, false⟩, ?_⟩
  simp [Engine.visible, Table.subjectExempt, hrls, hforce, hpol]

/-- No fabrication of access: whenever the engine grants a non-exempt subject
access to a row under enabled RLS, an actual policy justifies it. -/
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

