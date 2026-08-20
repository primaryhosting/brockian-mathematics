/-
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA

/-- A row-level security policy: it says which principals are permitted to see which rows. -/
structure Policy (Principal Row : Type*) where
  /-- `permits p r` holds when the policy grants principal `p` access to row `r`. -/
  permits : Principal → Row → Prop

/-- A table of the isolation engine's model: a row-level-security (RLS) switch together with
the list of policies that are consulted when the switch is on. -/
structure Table (Principal Row : Type*) where
  /-- Whether row-level security is enabled for this table. -/
  rlsEnabled : Bool
  /-- The policies attached to the table (only consulted when `rlsEnabled = true`). -/
  policies : List (Policy Principal Row)

variable {Principal Row : Type*}

/-- Access semantics of the engine: when RLS is off every row is visible to every principal;
when RLS is on a row is visible only if some attached policy permits it. -/
def Table.Visible (t : Table Principal Row) (p : Principal) (r : Row) : Prop :=
  t.rlsEnabled = false ∨ ∃ pol ∈ t.policies, pol.permits p r

/-- A row is *protected* when at least one principal is denied access to it. -/
def Table.RowProtected (t : Table Principal Row) (r : Row) : Prop :=
  ∃ p : Principal, ¬ t.Visible p r

/-- The set of rows that enjoy some protection. -/
def Table.protectedRows (t : Table Principal Row) : Set Row :=
  {r | t.RowProtected r}

namespace Invariant

/-- **Main invariant.** If row-level security is switched off on a table, then no row of that
table is protected: every principal can see every row.

(The core step is just `Or.inl`, i.e. `Mathlib`'s disjunction introduction, after unfolding the
access semantics; `not_exists`-style reasoning is handled by `simp`.) -/
theorem rls_off_implies_no_row_protection
    (t : Table Principal Row) (h : t.rlsEnabled = false) :
    ∀ r : Row, ¬ t.RowProtected r := by
  rintro r ⟨p, hp⟩
  exact hp (Or.inl h)

/-- Equivalent phrasing: with RLS off the set of protected rows is empty. -/
theorem protectedRows_eq_empty_of_rls_off
    (t : Table Principal Row) (h : t.rlsEnabled = false) :
    t.protectedRows = (∅ : Set Row) := by
  ext r
  simpa [Table.protectedRows] using rls_off_implies_no_row_protection t h r

/-- Equivalent phrasing: with RLS off, every principal sees every row. -/
theorem visible_of_rls_off
    (t : Table Principal Row) (h : t.rlsEnabled = false) (p : Principal) (r : Row) :
    t.Visible p r :=
  Or.inl h

/-- Converse (completeness of the invariant): if some row is protected, RLS must be on. -/
theorem rls_on_of_row_protected
    (t : Table Principal Row) {r : Row} (h : t.RowProtected r) :
    t.rlsEnabled = true := by
  rcases h with ⟨p, hp⟩
  cases hb : t.rlsEnabled with
  | false => exact absurd (Or.inl hb) hp
  | true => rfl

/-- Exact characterisation of protection in the model: a row is protected precisely when RLS is
on and some principal is permitted by none of the attached policies. -/
theorem rowProtected_iff (t : Table Principal Row) (r : Row) :
    t.RowProtected r ↔
      t.rlsEnabled = true ∧ ∃ p : Principal, ∀ pol ∈ t.policies, ¬ pol.permits p r := by
  constructor
  · intro h
    refine ⟨rls_on_of_row_protected t h, ?_⟩
    rcases h with ⟨p, hp⟩
    exact ⟨p, fun pol hpol hperm => hp (Or.inr ⟨pol, hpol, hperm⟩)⟩
  · rintro ⟨hon, p, hp⟩
    refine ⟨p, ?_⟩
    rintro (hoff | ⟨pol, hpol, hperm⟩)
    · exact absurd (hon.symm.trans hoff) (by simp)
    · exact hp pol hpol hperm

/-- Switching RLS off on any table wipes out all row protection. -/
theorem protectedRows_disableRls_eq_empty (t : Table Principal Row) :
    ({t with rlsEnabled := false} : Table Principal Row).protectedRows = (∅ : Set Row) :=
  protectedRows_eq_empty_of_rls_off _ rfl

/-- The invariant is not vacuous: with RLS *on* and no permitting policy, a row really is
protected. -/
theorem exists_rowProtected_of_rls_on :
    ∃ t : Table Bool Unit, t.rlsEnabled = true ∧ t.RowProtected () := by
  refine ⟨⟨true, []⟩, rfl, ?_⟩
  exact (rowProtected_iff _ ()).2 ⟨rfl, true, by simp⟩

end Invariant

end PCA

