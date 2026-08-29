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

/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Invariant

universe u v

/-- A row-level-security policy: it says which principals may see which rows. -/
structure Policy (Row : Type u) (Principal : Type v) where
  /-- `permits p r` holds when the policy grants principal `p` access to row `r`. -/
  permits : Principal → Row → Prop

/-- A table of the isolation engine's model: a row-level-security switch
together with the policies that are installed on the table. -/
structure Table (Row : Type u) (Principal : Type v) where
  /-- Whether row-level security is switched on for this table. -/
  rlsEnabled : Bool
  /-- The policies installed on the table. -/
  policies : List (Policy Row Principal)

variable {Row : Type u} {Principal : Type v}

/-- The visibility semantics of the engine: when row-level security is off every
row is visible to every principal; when it is on, a row is visible to a principal
exactly when some installed policy permits it. -/
def Visible (t : Table Row Principal) (p : Principal) (r : Row) : Prop :=
  t.rlsEnabled = false ∨ ∃ pol ∈ t.policies, pol.permits p r

/-- A row is *protected* when some principal is denied access to it. -/
def RowProtected (t : Table Row Principal) (r : Row) : Prop :=
  ∃ p : Principal, ¬ Visible t p r

/-- **Main invariant.** If row-level security is switched off on a table, then no
row of that table is protected: every principal can see every row. -/
theorem rls_off_implies_no_row_protection
    (t : Table Row Principal) (h : t.rlsEnabled = false) :
    ∀ r : Row, ¬ RowProtected t r := by
  rintro r ⟨p, hp⟩
  exact hp (Or.inl h)

/-- Equivalent phrasing: with row-level security off, every principal sees every row. -/
theorem rls_off_all_visible
    (t : Table Row Principal) (h : t.rlsEnabled = false) :
    ∀ (p : Principal) (r : Row), Visible t p r :=
  fun _ _ => Or.inl h

/-- Completeness counterpart: if row-level security is on and no installed policy
permits principal `p` to read row `r`, then that row is protected. -/
theorem rls_on_no_policy_row_protected
    (t : Table Row Principal) (r : Row) (p : Principal)
    (h : t.rlsEnabled = true)
    (hp : ∀ pol ∈ t.policies, ¬ pol.permits p r) :
    RowProtected t r := by
  refine ⟨p, ?_⟩
  rintro (hoff | ⟨pol, hmem, hper⟩)
  · rw [h] at hoff
    exact Bool.noConfusion hoff
  · exact hp pol hmem hper

/-- Sharp form: a protected row can exist only when row-level security is enabled. -/
theorem exists_protected_imp_rls_on
    (t : Table Row Principal) (h : ∃ r : Row, RowProtected t r) :
    t.rlsEnabled = true := by
  obtain ⟨r, hr⟩ := h
  cases hb : t.rlsEnabled with
  | false => exact absurd hr (rls_off_implies_no_row_protection t hb r)
  | true => rfl

end PCA.Invariant

